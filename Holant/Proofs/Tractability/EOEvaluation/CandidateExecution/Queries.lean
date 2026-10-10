import Holant.Proofs.Tractability.EOEvaluation.MatrixRefinement
import Holant.Proofs.Tractability.EOEvaluation.CandidatePairing


namespace Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Queries
open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing AffineMachine LocalAffineMachine.Relabel
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.TraversalCompletion.RationalLP
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ} (D : Source.Family s arity)

def value (r : Source.Input (s := s) (arity := arity)) : List Codec.CoordinateQuery :=
  List.ofFn (fun j : Fin (MatrixCompiler.raw D r).dimension => ⟨MatrixCompiler.value D r, j⟩)

def rawEncoding := pairEncoding Codec.inputEncoding UnaryBinary.unaryEncoding
def outputEncoding := framedListEncoding Codec.coordinateEncoding

private theorem encode_map_congr {A B C : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
    (f : C → A) (g : C → B) (h : ∀ c, ea.encode (f c) = eb.encode (g c)) (cs : List C) :
    framedListEncode ea (cs.map f) = framedListEncode eb (cs.map g) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, framedListEncode, h, ih]

def rawComputes : Computes Source.inputEncoding (framedListEncoding rawEncoding)
    (fun r => (List.range (RawColumns.columns r).length).map (fun j => (MatrixCompiler.value D r, j))) := by
  let ctx := Wiring.firstComputes (Source.inputEncoding (s:=s) (arity:=arity)) UnaryBinary.unaryEncoding
  let idx := Wiring.secondComputes (Source.inputEncoding (s:=s) (arity:=arity)) UnaryBinary.unaryEncoding
  exact WireLists.tabulate Source.inputEncoding rawEncoding _ MatrixCompiler.dimensionComputes _
    (pairComputes (ctx.andThen (MatrixCompiler.computes D)) idx)

def computes : Computes Source.inputEncoding outputEncoding (value D) := by
  refine recode (rawComputes D) id (fun _ => rfl) ?_
  intro r
  rw [DensePrograms.range_map]
  simp only [value, outputEncoding, framedListEncoding, List.ofFn_eq_map]
  exact encode_map_congr rawEncoding Codec.coordinateEncoding _ _ (fun _ => rfl) _

theorem length (r : Source.Input (s := s) (arity := arity)) :
    (value D r).length = (RawColumns.columns r).length := by simp [value, MatrixCompiler.raw]

theorem query_at (r : Source.Input (s := s) (arity := arity))
    (j : Fin (MatrixCompiler.raw D r).dimension) :
    (value D r).get ⟨j.val, by simpa [length, MatrixCompiler.raw] using j.isLt⟩ =
      ⟨MatrixCompiler.value D r, j⟩ := by simp [value, List.get_eq_getElem]

theorem positive_at (r : Source.Input (s := s) (arity := arity))
    (j : Fin (MatrixCompiler.raw D r).dimension) :
    Codec.Positive (MatrixCompiler.value D r).val j ↔
      Relaxation.Candidate (Source.network D r) (ColumnOrder.order r j).1 (ColumnOrder.order r j).2 :=
  MatrixRefinement.positive_iff D r j

theorem count_bound (r : Source.Input (s := s) (arity := arity)) :
    (value D r).length ≤ Source.localBudget s arity * (Source.inputEncoding.encode r).length := by
  rw [length, RawColumns.length_eq]
  exact Source.coordinate_bound r

theorem primitive_bound (r : Source.Input (s := s) (arity := arity)) :
    primitiveCost (computes D).machine ((computes D).outputs r).steps
      (some (Turing.initList (computes D).machine.computer (Source.inputEncoding.encode r))) ≤
        (primitivePolynomial (computes D)).eval (Source.inputEncoding.encode r).length :=
  computes_primitive_cost (computes D) r

end
end Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Queries
