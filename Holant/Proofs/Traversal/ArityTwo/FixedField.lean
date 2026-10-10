import Holant.Proofs.Traversal.ArityTwo.Components
import Holant.Complexity.FixedFieldMachines.StackEvaluatorBridge


open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines

namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.FixedField
open Holant Holant.Algebraic Holant.Complexity Computability Turing
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open FixedFieldMachines.StackEvaluatorBridge
open scoped BigOperators
variable {A K : Type} [Fintype A] [DecidableEq A] [Field K] [Algebra ℚ K] {n : ℕ}

noncomputable def coefficients (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ) : A → K :=
  fun a => F.decode (coords a)

/-- The runtime constants are rational coordinate words, fixed before input. -/
def literals (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ) :
    Kernels.Literals F.encoding (coefficients F coords) where
  table.words a := (vectorEncoding n).encode (coords a)
  table.correct a := (F.encoding_decode (coords a)).symm
  zeroWord := (vectorEncoding n).encode 0
  oneWord := (vectorEncoding n).encode F.unitCode
  zero_correct := by simpa using (F.encoding_decode (0 : Fin n → ℚ)).symm
  one_correct := by simpa using (F.encoding_decode F.unitCode).symm

def labelWidth (labels : Encoding A Bool) : ℕ := ∑ a, (labels.encode a).length

theorem label_le (labels : Encoding A Bool) (a : A) :
    (labels.encode a).length ≤ labelWidth labels :=
  Finset.single_le_sum (f := fun a => (labels.encode a).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

noncomputable def machine (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ)
    (labels : Encoding A Bool) :=
  fieldInterpreter F labels (labelWidth labels) (coefficients F coords) (literals F coords)

noncomputable def width (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ) (L : ℕ) :=
  ArithmeticSize.bitBound F (ArithmeticSize.withUnit F coords) L + literalWidth (literals F coords)

noncomputable def widthPolynomial (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ) : Polynomial ℕ :=
  let table := ArithmeticSize.withUnit F coords
  let M := F.toArithmeticData.familyBound table
  let D := F.toArithmeticData.familyDenominator table
  Polynomial.C n * (4 * (Polynomial.X + Polynomial.C M.size +
    Polynomial.X * Polynomial.C (n*n*M*M).size +
    (2*Polynomial.X+1)*Polynomial.C D.size+3)+1) +
    Polynomial.C (literalWidth (literals F coords))

@[simp] theorem widthPolynomial_eval (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ) (L : ℕ) :
    (widthPolynomial F coords).eval L = width F coords L := by
  simp [widthPolynomial,width,ArithmeticSize.bitBound]

noncomputable def runtimeBound (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ)
    (labels : Encoding A Bool) (L : ℕ) :=
  L * Interpreter.instructionBound (labelWidth labels) F.encoding (fieldProviders F)
    (width F coords L) L + 6*width F coords L+16

noncomputable def runtimePolynomial (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ)
    (labels : Encoding A Bool) : Polynomial ℕ :=
  let W := widthPolynomial F coords
  let P := fieldProviders F
  let instruction := P.add.time.comp (3*W+1) + P.mul.time.comp (3*W+1) +
    14*W+18+(2*W+4)*Polynomial.C (2^18)+3+
    Polynomial.C (2*(labelWidth labels+6))+4*((2*W+2)*Polynomial.X+1)+9
  Polynomial.X*instruction+6*W+16

@[simp] theorem runtimePolynomial_eval (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ)
    (labels : Encoding A Bool) (L : ℕ) :
    (runtimePolynomial F coords labels).eval L = runtimeBound F coords labels L := by
  simp [runtimePolynomial,runtimeBound,Interpreter.instructionBound,Kernels.timeBound]

theorem trace_width (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ)
    (cs : List (Component A)) :
    ∀ x ∈ componentsTrace (coefficients F coords) cs,
      (F.encoding.encode x).length ≤
        ArithmeticSize.bitBound F (ArithmeticSize.withUnit F coords) (componentsBudget cs) := by
  have h := components_bound (fun a => F.decode (ArithmeticSize.withUnit F coords a)) none
    (ArithmeticSize.decode_withUnit_none F coords) (coefficients F coords)
    (fun a => ArithmeticSize.Bound.coefficient (some a)) cs
  exact fun x hx => (h.2 x hx).encoded_length_le F (ArithmeticSize.withUnit F coords)

/-- Full exact execution, with no semantic-run or trace-size premise. -/
theorem evaluate_components_code (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ)
    (labels : Encoding A Bool) (cs : List (Component A)) :
    ∃ time, time ≤ (runtimePolynomial F coords labels).eval
        ((codeEncoding labels).encode (componentsCode cs)).length ∧
      Kernels.Executes (machine F coords labels)
        ((codeEncoding labels).encode (componentsCode cs))
        (F.encoding.encode (evaluateComponents (coefficients F coords) cs)) time := by
  let L := ((codeEncoding labels).encode (componentsCode cs)).length
  let W := width F coords L
  have hc : (componentsCode cs).length ≤ L := by
    have h := framedListEncoding_length_lower (opEncoding labels) (componentsCode cs)
    change 2*(componentsCode cs).length+1 ≤ L at h
    omega
  have hb : componentsBudget cs ≤ L := (componentsBudget_le_code cs).trans hc
  have hw : literalWidth (literals F coords) ≤ W := Nat.le_add_left _ _
  have ht : ∀ x ∈ componentsTrace (coefficients F coords) cs, (F.encoding.encode x).length ≤ W := by
    intro x hx
    exact ((trace_width F coords cs x hx).trans
      (ArithmeticSize.bitBound_mono F (ArithmeticSize.withUnit F coords) hb)).trans (Nat.le_add_right _ _)
  obtain ⟨time,htime,hr⟩ := Interpreter.value_of_run labels (labelWidth labels) F.encoding
    (coefficients F coords) (literals F coords) (fieldProviders F) (label_le labels) W
    (fun a => (literal_le (literals F coords) a).trans hw)
    ((zero_le (literals F coords)).trans hw) ((one_le (literals F coords)).trans hw)
    (componentsCode cs) (evaluateComponents (coefficients F coords) cs)
    (componentsTrace (coefficients F coords) cs) (run_components (coefficients F coords) cs []) ht
  have hm := instructionBound_mono_height (labelWidth labels) F.encoding (fieldProviders F) W hc
  refine ⟨time, ?_, hr⟩
  rw [runtimePolynomial_eval]
  exact htime.trans (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul hc hm) (6*W)) 16)

/-- Primitive operations are charged using the actual fixed machine syntax. -/
noncomputable def primitivePolynomial (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ)
    (labels : Encoding A Bool) : Polynomial ℕ :=
  runtimePolynomial F coords labels * Polynomial.C (machine F coords labels).primitiveBudget

theorem evaluate_components_with_primitive_cost (F : Algebraic.FixedField K n)
    (coords : A → Fin n → ℚ) (labels : Encoding A Bool) (cs : List (Component A)) :
    ∃ time, time ≤ (runtimePolynomial F coords labels).eval
        ((codeEncoding labels).encode (componentsCode cs)).length ∧
      Kernels.Executes (machine F coords labels)
        ((codeEncoding labels).encode (componentsCode cs))
        (F.encoding.encode (evaluateComponents (coefficients F coords) cs)) time ∧
      primitiveCost (machine F coords labels) time (some (initList (machine F coords labels).computer
        ((codeEncoding labels).encode (componentsCode cs)))) ≤
        (primitivePolynomial F coords labels).eval ((codeEncoding labels).encode (componentsCode cs)).length := by
  obtain ⟨time,ht,hr⟩ := evaluate_components_code F coords labels cs
  refine ⟨time,ht,hr,?_⟩
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    (primitiveCost_le (machine F coords labels) time _).trans (Nat.mul_le_mul_right _ ht)

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.FixedField
