import Holant.Proofs.Traversal.LocalAffineSupport.Correctness
import Holant.Complexity.FixedFieldMachines.PrimitiveCost


namespace Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Bounds
open Holant Holant.Tractable Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine
noncomputable section

theorem bool_length (a : Bool) : (encodingBoolBool.encode a).length = 1 := rfl

theorem bits_length (xs : List Bool) : (EncodedTable.bitsEncoding.encode xs).length = 4*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [EncodedTable.bitsEncoding, framedListEncoding, framedListEncode,
      List.length_cons, List.length_append, Holant.Algebraic.frame_length,
      bool_length] at *
    omega

theorem row_length (r : EncodedTable.Row) :
    (EncodedTable.rowEncoding.encode r).length = 4*r.2.length+4 := by
  rw [EncodedTable.rowEncoding, pairEncoding_length, bits_length, bool_length]
  omega

theorem rows_length (n : ℕ) (rows : List EncodedTable.Row)
    (h : ∀ row ∈ rows, row.2.length = n) :
    (EncodedTable.rowsEncoding.encode rows).length = (8*n+10)*rows.length+1 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have hh := h row (by simp)
    have ht := ih (fun row hr => h row (List.mem_cons_of_mem _ hr))
    change (true :: Holant.Algebraic.frame (EncodedTable.rowEncoding.encode row) ++
      EncodedTable.rowsEncoding.encode rows).length = _
    simp only [List.length_cons, List.length_append, Holant.Algebraic.frame_length, row_length, hh, ht]
    ring

theorem matrix_length (d : Codec.Matrix) (h : Codec.Rectangular d) :
    (Codec.encoding.encode d).length = 2*d.1+2+(8*d.1+10)*d.2.length := by
  rw [Codec.encoding, pairEncoding_length, rows_length d.1 d.2 h]
  simp only [UnaryBinary.unaryEncoding, List.length_replicate]
  ring

variable {s b : ℕ} {arity : ℕ → ℕ} (D : LocalAffineLabels.Family s b arity)

def outputPolynomial : Polynomial ℕ :=
  Polynomial.C (16*LocalAffineLabels.rowBudget D)*Polynomial.X^2 +
    Polynomial.C (10*LocalAffineLabels.rowBudget D+4)*Polynomial.X + 2

theorem output_length (r : RawRows.Input (s:=s) (b:=b) (arity:=arity)) :
    (Codec.encoding.encode (Matrix.value D r)).length ≤
      (outputPolynomial D).eval (RawClosedNetwork.encoding.encode r.val).length := by
  let L := (RawClosedNetwork.encoding.encode r.val).length
  have hc : r.val.vertices.length+r.val.edges.length ≤ L := r.val.counts_le_encoded_length
  have hn : (Matrix.value D r).1 ≤ 2*L := by
    change 2*r.val.edges.length ≤ 2*L
    omega
  have hr : (Matrix.value D r).2.length ≤ L*LocalAffineLabels.rowBudget D :=
    by
      calc
        _ ≤ (r.val.vertices.length+r.val.edges.length)*LocalAffineLabels.rowBudget D := by
          simpa [Matrix.value, Matrix.materialize] using RawRows.rows_bound D r
        _ ≤ L*LocalAffineLabels.rowBudget D := Nat.mul_le_mul_right _ hc
  calc
    (Codec.encoding.encode (Matrix.value D r)).length =
        2*(Matrix.value D r).1+2+(8*(Matrix.value D r).1+10)*(Matrix.value D r).2.length :=
      matrix_length _ (Matrix.value_rectangular D r)
    _ ≤ 2*(2*L)+2+(8*(2*L)+10)*(L*LocalAffineLabels.rowBudget D) := by gcongr
    _ = (outputPolynomial D).eval L := by simp [outputPolynomial]; ring

/-- These polynomials are constructed by composition of actual finite machines;
all fixed local tables, including rowBudget, are fixed program data. -/
def timePolynomial : Polynomial ℕ := (Matrix.computes D).time
def primitiveBound : Polynomial ℕ := primitivePolynomial (Matrix.computes D)

theorem time_bound (r : RawRows.Input (s:=s) (b:=b) (arity:=arity)) :
    ((Matrix.computes D).outputs r).steps ≤
      (timePolynomial D).eval (RawClosedNetwork.encoding.encode r.val).length :=
  ((Matrix.computes D).outputs r).steps_le_m

theorem primitive_bound (r : RawRows.Input (s:=s) (b:=b) (arity:=arity)) :
    primitiveCost (Matrix.computes D).machine ((Matrix.computes D).outputs r).steps
      (some (Turing.initList (Matrix.computes D).machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitiveBound D).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (Matrix.computes D) r

/-- The same physical run produces the faithful support-matrix codec. -/
theorem execution (r : RawRows.Input (s:=s) (b:=b) (arity:=arity)) :
    ∃ t, t ≤ (timePolynomial D).eval (RawClosedNetwork.encoding.encode r.val).length ∧
      StackProtocol.RunsExactly (Matrix.computes D).machine.computer.step
        (Turing.initList (Matrix.computes D).machine.computer (RawClosedNetwork.encoding.encode r.val))
        (Turing.haltList (Matrix.computes D).machine.computer (Codec.encoding.encode (Matrix.value D r))) t :=
  ⟨((Matrix.computes D).outputs r).steps, time_bound D r,
    ((Matrix.computes D).outputs r).evals_in_steps⟩

end
end Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Bounds
