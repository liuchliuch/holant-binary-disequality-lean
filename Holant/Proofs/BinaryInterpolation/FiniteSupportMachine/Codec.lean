import Holant.Proofs.Tractability.AffineMachine.ConstraintRefinement
import Holant.Proofs.Algorithms.LocalAffine.SupportSolver


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Codec

open Computability Holant.Tractable AffinePhase TwoTranslate Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open EncodedTable (Row bitsEncoding rowEncoding rowsEncoding)

abbrev Matrix := ℕ × List Row
def encoding := pairEncoding UnaryBinary.unaryEncoding rowsEncoding
def lift (d : Matrix) : EncodedTable.Data := (d.1, d.2, 0, [], [])
def support (d : Matrix) : AffineSystem d.1 := EncodedTable.support (lift d)
def Rectangular (d : Matrix) : Prop := ∀ r ∈ d.2, r.2.length = d.1

def storedRow {n : ℕ} (S : AffineSystem n) (r : Fin S.rows) : Row :=
  (decide (S.rhs r = 1), List.ofFn (fun j => decide (S.matrix r j = 1)))
def pack {n : ℕ} (S : AffineSystem n) : Matrix := (n, List.ofFn (storedRow S))

theorem pack_rectangular {n : ℕ} (S : AffineSystem n) : Rectangular (pack S) := by
  simp [Rectangular, pack, storedRow]

@[simp] theorem support_pack {n : ℕ} (S : AffineSystem n) : support (pack S) = S := by
  let Q : QuadraticPhase n := ⟨0, fun _ => 0, fun _ _ => 0, fun _ _ _ => Or.inl rfl⟩
  let T := Dense.snapshot S Q
  have he : EncodedTable.support (EncodedTable.store T) = support (pack S) := by
    have hs : (fun r : Fin S.rows =>
        (decide (T.support.rhs r = 1), List.ofFn (fun j => decide (T.support.matrix r j = 1)))) =
        storedRow S := by
      funext r
      simp only [T, Dense.Table.support, Dense.snapshot, List.Vector.get_ofFn, storedRow]
    unfold EncodedTable.store
    erw [hs]
    rfl
  exact he.symm.trans ((ReadRefinement.store_support T).trans (Dense.support_snapshot S Q))

def normalizeRow (n : ℕ) (r : Row) : Row :=
  (r.1, (List.range n).map (fun j => r.2.getD j false))
def normalize (d : Matrix) : Matrix := (d.1, d.2.map (normalizeRow d.1))

theorem normalized_rectangular (d : Matrix) : Rectangular (normalize d) := by
  intro r hr
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
  simp [normalizeRow, normalize]

theorem pack_support (d : Matrix) : pack (support d) = normalize d := by
  have hb (b : Bool) : decide (FiniteCore.bit2 b = 1) = b := by cases b <;> decide
  refine Prod.ext (by rfl) ?_
  change List.ofFn (fun r : Fin d.2.length =>
    (decide (FiniteCore.bit2 (d.2.get r).1 = 1),
      List.ofFn (fun j : Fin d.1 => decide (FiniteCore.bit2 ((d.2.get r).2.getD j.val false) = 1)))) = _
  simp only [hb]
  calc
    _ = (List.ofFn d.2.get).map (normalizeRow d.1) := by
      rw [List.map_ofFn]
      congr 1; funext r
      change (_, _) = (normalizeRow d.1 (d.2.get r))
      simp only [normalizeRow, DensePrograms.range_map]
    _ = d.2.map (normalizeRow d.1) := by rw [List.ofFn_get]

theorem normalize_eq (d : Matrix) (h : Rectangular d) : normalize d = d := by
  refine Prod.ext (by rfl) ?_
  change List.map (normalizeRow d.1) d.2 = d.2
  conv_rhs => rw [← List.map_id d.2]
  apply List.map_congr_left
  intro r hr
  refine Prod.ext (by rfl) ?_
  rw [normalizeRow, DensePrograms.range_map]
  exact ReadRefinement.ofFn_getD_length r.2 false (h r hr)

@[simp] theorem support_normalize (d : Matrix) : support (normalize d) = support d := by
  have he : (pack (support d)).2 = (normalize d).2 := congrArg Prod.snd (pack_support d)
  change support (d.1, (normalize d).2) = support d
  rw [← he]
  exact support_pack (support d)

theorem faithful (d : Matrix) : encoding.decode (encoding.encode d) = some d :=
  encoding.decode_encode d

noncomputable def dimension : Computes encoding UnaryBinary.unaryEncoding Prod.fst :=
  Wiring.firstComputes _ _
noncomputable def rows : Computes encoding rowsEncoding Prod.snd := Wiring.secondComputes _ _
noncomputable def liftComputes : Computes encoding EncodedTable.encoding lift :=
  pairComputes dimension (pairComputes rows
    (constantComputes encoding EncodedTable.phaseEncoding (0, [], [])))

noncomputable def normalizeRowComputes :
    Computes (pairEncoding encoding rowEncoding) rowEncoding (fun x => normalizeRow x.1.1 x.2) := by
  let ctx := Wiring.firstComputes encoding rowEncoding
  let row := Wiring.secondComputes encoding rowEncoding
  let ea := pairEncoding encoding rowEncoding
  let old := Wiring.firstComputes ea UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes ea UnaryBinary.unaryEncoding
  let coeffs := row.andThen (Wiring.secondComputes encodingBoolBool bitsEncoding)
  let bit := AccessPrograms.get encodingBoolBool false (old.andThen coeffs) j
  exact pairComputes (row.andThen (Wiring.firstComputes encodingBoolBool bitsEncoding))
    (WireLists.tabulate ea encodingBoolBool (fun x => x.1.1)
      (ctx.andThen dimension) _ bit)

noncomputable def normalizeComputes : Computes encoding encoding normalize :=
  pairComputes dimension (AccessPrograms.map rowEncoding rowEncoding rows
    (fun d r => normalizeRow d.1 r) normalizeRowComputes)

theorem normalize_primitive (d : Matrix) :
    primitiveCost normalizeComputes.machine (normalizeComputes.outputs d).steps
      (some (Turing.initList normalizeComputes.machine.computer (encoding.encode d))) ≤
        (primitivePolynomial normalizeComputes).eval (encoding.encode d).length :=
  computes_primitive_cost normalizeComputes d

end Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Codec
