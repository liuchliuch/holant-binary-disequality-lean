import Holant.Proofs.Tractability.ProductMachine.ExpressionEncoding
import Holant.Proofs.Tractability.ProductMachine.SymbolicElimination
import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Evaluation.Field
import Holant.Complexity.FixedFieldMachines.PrimitiveCost
import Holant.Algebraic.EncodingLowerBounds


namespace Holant.LocalDrafts.Tractability.ProductMachine.FieldInterpreter

open Turing Computability Holant.Complexity BinaryCompose Holant.Algebraic
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open FixedFieldMachines.StackEvaluatorBridge

variable {A K : Type} [Fintype A] [DecidableEq A] [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (table : A → Fin d → ℚ) (labels : Encoding A Bool) (C : ℕ)

noncomputable def coefficients := fun a => F.decode (table a)

def literals : Kernels.Literals F.encoding (coefficients F table) :=
  GraphCodeMachine.Components.Evaluation.literals F table

noncomputable def machine := fieldInterpreter F labels C (coefficients F table) (literals F table)

noncomputable def width (L : ℕ) :=
  ArithmeticSize.bitBound F (ArithmeticSize.withUnit F table) L + literalWidth (literals F table)

noncomputable def widthPolynomial : Polynomial ℕ :=
  GraphCodeMachine.Components.Evaluation.widthPolynomial F table

@[simp] theorem widthPolynomial_eval (L : ℕ) :
    (widthPolynomial F table).eval L = width F table L := by
  exact GraphCodeMachine.Components.Evaluation.widthPolynomial_eval F table L

/-- Applies to the result AND every operand/result in the compiled execution. -/
theorem encoded_trace_bound (e : Expr A) (L : ℕ) (he : e.size ≤ L) :
    (F.encoding.encode (e.eval (coefficients F table))).length ≤ width F table L ∧
    ∀ x ∈ e.trace (coefficients F table), (F.encoding.encode x).length ≤ width F table L := by
  let family := fun a => F.decode (ArithmeticSize.withUnit F table a)
  have hunit : family none = 1 := ArithmeticSize.decode_withUnit_none F table
  have h := e.arithmetic_bound (coefficients F table) family none hunit
    (fun a => ArithmeticSize.family_bound F table ⟨a, rfl⟩)
  have bound (x : K) (hx : ArithmeticSize.Bound family e.size x) :
      (F.encoding.encode x).length ≤ width F table L := by
    exact ((hx.encoded_length_le F (ArithmeticSize.withUnit F table)).trans
      (ArithmeticSize.bitBound_mono F (ArithmeticSize.withUnit F table) he)).trans (Nat.le_add_right _ _)
  exact ⟨bound _ h.1, fun x hx => bound x (h.2 x hx)⟩

/-- Numerator/denominator bit heights in every actual intermediate coordinate,
including every arithmetic operand, are bounded by the derived vector width. -/
theorem coordinate_trace_bound (e : Expr A) (L : ℕ) (he : e.size ≤ L) :
    (∀ i : Fin d, rationalBitHeight (F.decode.symm (e.eval (coefficients F table)) i) ≤ width F table L) ∧
    ∀ x ∈ e.trace (coefficients F table), ∀ i : Fin d,
      rationalBitHeight (F.decode.symm x i) ≤ width F table L := by
  have h := encoded_trace_bound F table e L he
  exact ⟨fun i => (field_coordinate_height_le_encoded_length F _ i).trans h.1,
    fun x hx i => (field_coordinate_height_le_encoded_length F x i).trans (h.2 x hx)⟩

noncomputable def runtimePolynomial : Polynomial ℕ :=
  let W := widthPolynomial F table
  let P := fieldProviders F
  let instruction := P.add.time.comp (3 * W + 1) + P.mul.time.comp (3 * W + 1) +
    14 * W + 18 + (2 * W + 4) * Polynomial.C (2 ^ 18) + 3 +
    Polynomial.C (2 * (C + 6)) + 4 * ((2 * W + 2) * Polynomial.X + 1) + 9
  Polynomial.X * instruction + 6 * W + 16

@[simp] theorem runtimePolynomial_eval (L : ℕ) :
    (runtimePolynomial F table C).eval L =
      L * Interpreter.instructionBound C F.encoding (fieldProviders F) (width F table L) L +
        6 * width F table L + 16 := by
  simp [runtimePolynomial, Interpreter.instructionBound, Kernels.timeBound]

/-- Every timed run belongs to the SAME fixed finite Boolean-stack interpreter.
No per-expression machine, supplied trace bound, or field oracle is used. -/
theorem execute (hlabels : ∀ a, (labels.encode a).length ≤ C) (e : Expr A)
    (L : ℕ) (he : e.size ≤ L) :
    ∃ time, time ≤ (runtimePolynomial F table C).eval L ∧
      Kernels.Executes (machine F table labels C)
        ((Expr.encoding labels).encode e) (F.encoding.encode (e.eval (coefficients F table))) time := by
  let W := width F table L
  have hw : literalWidth (literals F table) ≤ W := Nat.le_add_left _ _
  obtain ⟨time, ht, hr⟩ := Interpreter.value_of_run labels C F.encoding
    (coefficients F table) (literals F table) (fieldProviders F) hlabels W
    (fun a => (literal_le (literals F table) a).trans hw)
    ((zero_le (literals F table)).trans hw) ((one_le (literals F table)).trans hw)
    e.code (e.eval (coefficients F table)) (e.trace (coefficients F table))
    (e.run_code (coefficients F table) []) (encoded_trace_bound F table e L he).2
  have hc : e.code.length ≤ L := by simpa [Expr.code_length] using he
  have hm := instructionBound_mono_height C F.encoding (fieldProviders F) W hc
  refine ⟨time, ?_, hr⟩
  rw [runtimePolynomial_eval]
  exact ht.trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul hc hm) (6 * W)) 16)

noncomputable def computes (hlabels : ∀ a, (labels.encode a).length ≤ C) :
    Computes (Expr.encoding labels) F.encoding (Expr.eval (coefficients F table)) where
  machine := machine F table labels C
  time := runtimePolynomial F table C
  outputs e := by
    let h := execute F table labels C hlabels e
      ((Expr.encoding labels).encode e).length (e.size_le_encoded labels)
    -- Select only the run-length certificate of this already fixed machine.
    exact {
      steps := Classical.choose h
      evals_in_steps := (Classical.choose_spec h).2
      steps_le_m := (Classical.choose_spec h).1 }

theorem primitive_bound (hlabels : ∀ a, (labels.encode a).length ≤ C) (e : Expr A) :
    let w := computes F table labels C hlabels
    FixedFieldMachines.primitiveCost w.machine (w.outputs e).steps
      (some (initList w.machine.computer ((Expr.encoding labels).encode e))) ≤
        (FixedFieldMachines.primitivePolynomial w).eval ((Expr.encoding labels).encode e).length :=
  FixedFieldMachines.computes_primitive_cost (computes F table labels C hlabels) e

/-- Concrete Product program, with a quadratic structural parameter. This
closes the scalar interpreter obligation, not the raw factor compiler obligation. -/
theorem execute_product (hlabels : ∀ a, (labels.encode a).length ≤ C)
    {n : ℕ} (fs : List (ProductElimination.LabelledFactor A n)) :
    ∃ time, time ≤ (runtimePolynomial F table C).eval (Symbolic.budget n fs.length) ∧
      Kernels.Executes (machine F table labels C)
        ((Expr.encoding labels).encode (Symbolic.compile fs))
        (F.encoding.encode (ProductElimination.evaluate
          (fs.map (ProductElimination.LabelledFactor.realize (coefficients F table))))) time := by
  simpa only [Symbolic.compile_eval] using execute F table labels C hlabels
    (Symbolic.compile fs) (Symbolic.budget n fs.length) (Symbolic.compile_size fs)

/-- Primitive instructions charged on the very same generated-code execution. -/
theorem execute_product_primitive (hlabels : ∀ a, (labels.encode a).length ≤ C)
    {n : ℕ} (fs : List (ProductElimination.LabelledFactor A n)) :
    ∃ time, time ≤ (runtimePolynomial F table C).eval (Symbolic.budget n fs.length) ∧
      Kernels.Executes (machine F table labels C)
        ((Expr.encoding labels).encode (Symbolic.compile fs))
        (F.encoding.encode (ProductElimination.evaluate
          (fs.map (ProductElimination.LabelledFactor.realize (coefficients F table))))) time ∧
      FixedFieldMachines.primitiveCost (machine F table labels C) time
        (some (initList (machine F table labels C).computer
          ((Expr.encoding labels).encode (Symbolic.compile fs)))) ≤
        (runtimePolynomial F table C).eval (Symbolic.budget n fs.length) *
          (machine F table labels C).primitiveBudget := by
  obtain ⟨t, ht, hr⟩ := execute_product F table labels C hlabels fs
  exact ⟨t, ht, hr, (FixedFieldMachines.primitiveCost_le _ _ _).trans
    (Nat.mul_le_mul_right _ ht)⟩

end Holant.LocalDrafts.Tractability.ProductMachine.FieldInterpreter
