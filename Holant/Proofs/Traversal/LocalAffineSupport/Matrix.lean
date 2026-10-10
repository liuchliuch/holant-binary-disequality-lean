import Holant.Proofs.Traversal.LocalAffineSupport.RawRows
import Holant.Proofs.BinaryInterpolation.FiniteSupportMachine.Codec
import Holant.Proofs.Tractability.AffineMachine.SparseRefinement


namespace Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Matrix
open Holant Holant.Tractable AffinePhase TwoTranslate Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine
noncomputable section

def materialize (n : ℕ) (rows : List RawBlocks.Row) : Codec.Matrix :=
  (n, rows.map (BlockAggregation.row n))

theorem rectangular (n : ℕ) (rows : List RawBlocks.Row) : Codec.Rectangular (materialize n rows) := by
  intro row hr
  obtain ⟨raw, _, rfl⟩ := List.mem_map.mp hr
  simp [BlockAggregation.row,materialize]

/-- One global coefficient is the sum of every local occurrence at its address;
no nodup assumption is used, and no Boolean OR replaces addition. -/
theorem coefficient (n : ℕ) (row : RawBlocks.Row) (j : Fin n) :
    FiniteCore.bit2 ((BlockAggregation.row n row).2.getD j.val false) =
      (row.2.map (fun k => if k = j.val then (1 : ZMod 2) else 0)).sum :=
  SparseRefinement.row_coefficient n row j

theorem repeated_address_cancels (a j : ℕ) (rest : List ℕ) :
    SparseRefinement.coefficient (a::a::rest) j = SparseRefinement.coefficient rest j := by
  have h (q : ZMod 2) : q+q = 0 := by fin_cases q <;> decide
  simp [SparseRefinement.coefficient, ← add_assoc, h]

theorem holds_materialize (n : ℕ) (rows : List RawBlocks.Row) (x : Word n) :
    (Codec.support (materialize n rows)).Holds x ↔
      ∀ row ∈ rows, RawBlocks.rowHolds (fun k => (List.ofFn x).getD k false) row := by
  change (∀ i : Fin (rows.map (BlockAggregation.row n)).length,
    (∑ j, FiniteCore.bit2 (((rows.map (BlockAggregation.row n)).get i).2.getD j.val false) *
      bitValue (ZMod 2) (x j)) = FiniteCore.bit2 ((rows.map (BlockAggregation.row n)).get i).1) ↔ _
  constructor
  · intro h row hr
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
    have hh := h ⟨i.val, by simpa using i.isLt⟩
    have he : (rows.map (BlockAggregation.row n)).get ⟨i.val, by simpa using i.isLt⟩ =
        BlockAggregation.row n row := by simp [← hi]
    rw [he] at hh
    exact (SparseRefinement.row_holds n row x).mp
      (by simpa only [FiniteCore.dot_eq, TwoTranslate.dot] using hh)
  · intro h i
    let j : Fin rows.length := ⟨i.val, by simpa using i.isLt⟩
    have hh := (SparseRefinement.row_holds n (rows.get j) x).mpr (h _ (List.get_mem rows j))
    simpa [FiniteCore.dot_eq, TwoTranslate.dot, List.get_eq_getElem, j] using hh

def sparseEncoding := pairEncoding UnaryBinary.unaryEncoding RawBlocks.rowsEncoding

def materializeComputes : Computes sparseEncoding Codec.encoding
    (fun x => materialize x.1 x.2) :=
  pairComputes (Wiring.firstComputes UnaryBinary.unaryEncoding RawBlocks.rowsEncoding)
    (mapListComputes UnaryBinary.unaryEncoding RawBlocks.rowEncoding EncodedTable.rowEncoding
      BlockAggregation.row BlockAggregation.rowComputes)

variable {s b : ℕ} {arity : ℕ → ℕ} (D : LocalAffineLabels.Family s b arity)

def dimensionComputes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    UnaryBinary.unaryEncoding (fun r => 2*r.val.edges.length) :=
  congrComputes ((pairComputes (edgeCountComputes s b arity) (edgeCountComputes s b arity)).andThen
    AccessPrograms.unaryAdd) (fun r => by simp [two_mul])

def value (r : RawRows.Input (s:=s) (b:=b) (arity:=arity)) : Codec.Matrix :=
  materialize (2*r.val.edges.length) (RawRows.value D r)

/-- The only runtime input is the original validated raw encoding. -/
def computes : Computes (RawClosedNetwork.validatedEncoding s b arity) Codec.encoding (value D) :=
  (pairComputes dimensionComputes (RawRows.computes D)).andThen materializeComputes

@[simp] theorem dimension (r : RawRows.Input (s:=s) (b:=b) (arity:=arity)) :
    (value D r).1 = 2*r.val.edges.length := rfl

theorem value_rectangular (r : RawRows.Input (s:=s) (b:=b) (arity:=arity)) :
    Codec.Rectangular (value D r) := rectangular _ _

theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity) Codec.encoding (value D) :=
  (computes D).inFP

end
end Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Matrix
