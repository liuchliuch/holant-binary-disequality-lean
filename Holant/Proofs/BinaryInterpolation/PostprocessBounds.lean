import Holant.Complexity.BinaryInterpolation.WeightCompiler.Combinators
import Holant.Complexity.BinaryInterpolation.PostprocessValue
import Holant.Complexity.BinaryInterpolation.StackInputExecution
import Holant.Complexity.BinaryInterpolation.RingFormulaMachine


namespace Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds
open Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open Holant.Algebraic
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

variable {A D K : Type} [CommSemiring K]
variable (coeff : A → K) (base : D → K) (unit : D) (hunit : base unit = 1)

include unit hunit in
/-- Formula literals may be a subset of the fixed original/spectral family.
There is no instance-dependent literal or answer in the finite instruction set. -/
theorem formula_bound (hlit : ∀ a, ArithmeticSize.Bound base 1 (coeff a))
    (p : RingFormula A) :
    ArithmeticSize.Bound base p.size (p.eval coeff) ∧
      ∀ x ∈ p.trace coeff, ArithmeticSize.Bound base p.size x := by
  induction p with
  | literal a => exact ⟨hlit a, by simp [RingFormula.trace]⟩
  | zero => exact ⟨ArithmeticSize.Bound.zero unit 1, by simp [RingFormula.trace]⟩
  | one => exact ⟨ArithmeticSize.Bound.one.mono unit hunit (by simp [RingFormula.size]),
      by simp [RingFormula.trace]⟩
  | add p q hp hq =>
    have he := (hp.1.mono unit hunit (show p.size ≤ p.size+q.size by omega)).add unit hunit
      (hq.1.mono unit hunit (show q.size ≤ p.size+q.size by omega))
    refine ⟨he, ?_⟩
    intro x hx
    simp only [RingFormula.trace, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx|hx)|hx|hx|hx
    · exact (hq.2 x hx).mono unit hunit (by simp [RingFormula.size]; omega)
    · exact (hp.2 x hx).mono unit hunit (by simp [RingFormula.size]; omega)
    · subst x; exact hp.1.mono unit hunit (by simp [RingFormula.size]; omega)
    · subst x; exact hq.1.mono unit hunit (by simp [RingFormula.size]; omega)
    · subst x; exact he
  | mul p q hp hq =>
    have he := (hp.1.mul hq.1).mono unit hunit (show p.size+q.size ≤ p.size+q.size+1 by omega)
    refine ⟨he, ?_⟩
    intro x hx
    simp only [RingFormula.trace, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx|hx)|hx|hx|hx
    · exact (hq.2 x hx).mono unit hunit (by simp [RingFormula.size]; omega)
    · exact (hp.2 x hx).mono unit hunit (by simp [RingFormula.size]; omega)
    · subst x; exact hp.1.mono unit hunit (by simp [RingFormula.size]; omega)
    · subst x; exact hq.1.mono unit hunit (by simp [RingFormula.size]; omega)
    · subst x; exact he

include unit hunit in
/-- An answer is multiplied by one bounded weight, then added once. The
accumulator budget grows additively, including every copied or erased operand. -/
theorem weighted_bound (hlit : ∀ a, ArithmeticSize.Bound base 1 (coeff a))
    (ps : List (RingFormula A × K)) (Y W U : ℕ) (a : K)
    (hsize : ∀ p ∈ ps, p.1.size ≤ W)
    (hanswer : ∀ p ∈ ps, ArithmeticSize.Bound base Y p.2)
    (ha : ArithmeticSize.Bound base U a) :
    ArithmeticSize.Bound base (U+ps.length*(Y+W+1)) (WeightedStack.value coeff ps a) ∧
      ∀ x ∈ WeightedStack.trace coeff ps a,
        ArithmeticSize.Bound base (U+ps.length*(Y+W+1)) x := by
  induction ps generalizing U a with
  | nil => simpa [WeightedStack.value, WeightedStack.trace] using ha
  | cons p ps ih =>
    rcases p with ⟨p,y⟩
    have hp := formula_bound coeff base unit hunit hlit p
    have hpW := hp.1.mono unit hunit (hsize (p,y) (by simp))
    have hy := hanswer (p,y) (by simp)
    have hprod := hy.mul hpW
    have hs := (hprod.mono unit hunit (show Y+W ≤ U+Y+W by omega)).add unit hunit
      (ha.mono unit hunit (show U ≤ U+Y+W by omega))
    have ht := ih (U+Y+W+1) (y*p.eval coeff+a)
      (fun q hq => hsize q (by simp [hq]))
      (fun q hq => hanswer q (by simp [hq])) hs
    have he : U+Y+W+1+ps.length*(Y+W+1) = U+(ps.length+1)*(Y+W+1) := by ring
    rw [he] at ht
    refine ⟨ht.1, ?_⟩
    let budget := U+(ps.length+1)*(Y+W+1)
    have hU : U ≤ budget := by dsimp [budget]; nlinarith
    have hY : Y ≤ budget := by dsimp [budget]; nlinarith
    have hW : W ≤ budget := by dsimp [budget]; nlinarith
    have hYW : Y+W ≤ budget := by dsimp [budget]; nlinarith
    have hS : U+Y+W+1 ≤ budget := by dsimp [budget]; nlinarith
    have hpTrace : ∀ x ∈ p.trace coeff, ArithmeticSize.Bound base budget x :=
      fun x hx => (hp.2 x hx).mono unit hunit ((hsize (p,y) (by simp)).trans hW)
    have hy' := hy.mono unit hunit hY
    have hp' := hpW.mono unit hunit hW
    have hprod' := hprod.mono unit hunit hYW
    have ha' := ha.mono unit hunit hU
    have hs' := hs.mono unit hunit hS
    intro x hx
    change ArithmeticSize.Bound base budget x
    simp only [WeightedStack.trace, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx|hx)|hx
    · exact hpTrace x hx
    · rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
      · exact hy'
      · exact hp'
      · exact hprod'
      · exact hprod'
      · exact ha'
      · exact hs'
    · exact ht.2 x hx

end

noncomputable section
variable {K D : Type} [Field K] [Algebra ℚ K] [Fintype D] {n : ℕ}
variable (F : FixedField K n) (base : D → Fin n → ℚ)
variable (unit : D) (hunit : F.decode (base unit) = 1)
variable (gamma rho : K)

def trace (geometric : Bool) (m : ℕ) (y : Fin (m+1) → K) : List K :=
  WeightedStack.trace (WeightFormulas.coefficients gamma rho)
    (List.ofFn (fun i => (WeightFormulas.weight geometric m i, y i))) 0 ++
  (WeightFormulas.totalDenominator geometric m).trace (WeightFormulas.coefficients gamma rho)

theorem reference_run (geometric : Bool) (m : ℕ) (y : Fin (m+1) → K) :
    run (WeightFormulas.coefficients gamma rho) (WeightCompiler.reference geometric m)
      (List.ofFn y) = some
      ([commonNumerator (queryDenominator (WeightFormulas.nodes geometric rho m)
          (WeightFormulas.scales gamma m)) y,
        commonDenominator (queryDenominator (WeightFormulas.nodes geometric rho m)
          (WeightFormulas.scales gamma m))], trace gamma rho geometric m y) := by
  have hw := WeightedStack.run_code (WeightFormulas.coefficients gamma rho)
    (List.ofFn (fun i => (WeightFormulas.weight geometric m i,y i))) 0 []
  simp only [List.map_ofFn, Function.comp_def, List.append_nil] at hw
  rw [weighted_numerator] at hw
  simp only [WeightCompiler.reference, run_append]
  simp only [run, step, bind, Option.bind_some, pure, List.nil_append]
  simp only [hw, Option.bind_some, RingFormula.run_code, WeightFormulas.eval_totalDenominator]
  simp [run, step, trace, List.append_assoc]

def budget (m Y : ℕ) := (m+1)*(Y+WeightFormulas.weightSize m+1)

include unit hunit in
theorem trace_bound
    (hlit : ∀ a, ArithmeticSize.Bound (fun d => F.decode (base d)) 1
      (WeightFormulas.coefficients gamma rho a))
    (geometric : Bool) (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i)) :
    ∀ x ∈ trace gamma rho geometric m y,
      ArithmeticSize.Bound (fun d => F.decode (base d)) (budget m Y) x := by
  have hw := weighted_bound (WeightFormulas.coefficients gamma rho)
    (fun d => F.decode (base d)) unit hunit hlit
    (List.ofFn (fun i => (WeightFormulas.weight geometric m i,y i))) Y
    (WeightFormulas.weightSize m) 0 0
    (by intro p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp; exact WeightFormulas.weight_size_le geometric m i)
    (by intro p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp; exact hy i)
    (ArithmeticSize.Bound.zero unit 0)
  have hd := formula_bound (WeightFormulas.coefficients gamma rho)
    (fun d => F.decode (base d)) unit hunit hlit (WeightFormulas.totalDenominator geometric m)
  have hsize : (WeightFormulas.totalDenominator geometric m).size ≤ budget m Y := by
    have h := WeightFormulas.totalDenominator_size_le geometric m
    unfold budget
    nlinarith
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · simpa [budget] using hw.2 x hx
  · exact (hd.2 x hx).mono unit hunit hsize

include unit hunit in
/-- Real interpreter execution with a width derived from every actual value.
The width is affine in budget(m,Y), hence polynomial whenever the physical
query answer certificates Y are polynomial in the original graph length. -/
theorem execute_reference
    (hlit : ∀ a, ArithmeticSize.Bound (fun d => F.decode (base d)) 1
      (WeightFormulas.coefficients gamma rho a))
    (geometric : Bool) (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i)) :
    let coeff := WeightFormulas.coefficients gamma rho
    let coords := fun a => F.decode.symm (coeff a)
    let W := ArithmeticSize.bitBound F base (budget m Y)
    let code := WeightCompiler.reference geometric m
    let lits := RingFormulaMachine.literals F coords
    ∃ time,
      time ≤ 2*((codeEncoding WeightCompiler.labels).encode code).length +
        2*((stackEncoding F.encoding).encode (List.ofFn y)).length + 6 +
        code.length*Interpreter.instructionBound
          (RingFormulaMachine.labelBound WeightCompiler.labels) F.encoding
          (fieldProviders F) W (m+1+code.length) ∧
      Kernels.Executes
        (StackInputInterpreter.machine (Kernels.machine lits (fieldProviders F))
          WeightCompiler.labels (RingFormulaMachine.labelBound WeightCompiler.labels))
        (Holant.Algebraic.frame ((codeEncoding WeightCompiler.labels).encode code) ++
          (stackEncoding F.encoding).encode (List.ofFn y))
        ((stackEncoding F.encoding).encode
          [commonNumerator (queryDenominator (WeightFormulas.nodes geometric rho m)
            (WeightFormulas.scales gamma m)) y,
           commonDenominator (queryDenominator (WeightFormulas.nodes geometric rho m)
            (WeightFormulas.scales gamma m))]) time := by
  dsimp only
  have hc : RingFormulaMachine.coefficients F
      (fun a => F.decode.symm (WeightFormulas.coefficients gamma rho a)) =
      WeightFormulas.coefficients gamma rho := by
    funext a
    exact F.decode.apply_symm_apply _
  have hY : Y ≤ budget m Y := by unfold budget; nlinarith
  have hOne : 1 ≤ budget m Y := by unfold budget; nlinarith
  have cert := certified_of_run F.encoding (WeightFormulas.coefficients gamma rho)
    (ArithmeticSize.bitBound F base (budget m Y))
    (m+1+(WeightCompiler.reference geometric m).length)
    (fun a => ((hlit a).mono unit hunit hOne).encoded_length_le F base)
    ((ArithmeticSize.Bound.zero unit (budget m Y)).encoded_length_le F base)
    ((ArithmeticSize.Bound.one.mono unit hunit (Nat.zero_le _)).encoded_length_le F base)
    (WeightCompiler.reference geometric m) (List.ofFn y) _ _
    (reference_run gamma rho geometric m y)
    (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
        exact ((hy i).mono unit hunit hY).encoded_length_le F base)
    (fun x hx => (trace_bound F base unit hunit gamma rho hlit geometric m Y y hy x hx).encoded_length_le F base)
    (by simp)
  have cert' := cert
  rw [← hc] at cert'
  exact StackInputInterpreter.execute WeightCompiler.labels
    (RingFormulaMachine.labelBound WeightCompiler.labels) F.encoding _
    (RingFormulaMachine.literals F (fun a => F.decode.symm (WeightFormulas.coefficients gamma rho a)))
    (fieldProviders F) (RingFormulaMachine.label_le WeightCompiler.labels) cert'

end
end Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds
