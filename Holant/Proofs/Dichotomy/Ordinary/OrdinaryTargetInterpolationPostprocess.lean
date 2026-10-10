import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationCode
import Holant.Proofs.BinaryInterpolation.PostprocessBounds

/-! Exact finite-target numerator/denominator semantics and all intermediate
field-value bounds for the emitted stack programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationPostprocess
open Holant Holant.Algebraic Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open scoped BigOperators
namespace F
export OrdinaryNegativeBinaryUnsignedInterpolationFormulas
  (coefficients weight totalDenominator divisors numerators eval_weight eval_totalDenominator weightSize
   weight_size totalDenominator_size)
end F
namespace C
export OrdinaryTargetInterpolationCode (reference)
end C
namespace B
export Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds (formula_bound weighted_bound)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K]
variable (gamma rho target : K)

def resultPair (m : ℕ) (y : Fin (m+1)→K) : K×K :=
  (commonNumerator (F.divisors gamma rho m) (fun i=>y i*F.numerators rho target m i),
    commonDenominator (F.divisors gamma rho m))

theorem weighted_numerator (m : ℕ) (y : Fin (m+1)→K) :
    WeightedStack.value (F.coefficients gamma rho target)
      (List.ofFn (fun i=>(F.weight m i,y i))) 0=(resultPair gamma rho target m y).1 := by
  rw [WeightedStack.value_eq_sum]
  simp only [zero_add,List.map_ofFn,Function.comp_apply,Fin.sum_ofFn,F.eval_weight,
    resultPair,commonNumerator]
  apply Finset.sum_congr rfl
  intro i _
  ring

def trace (m : ℕ) (y : Fin (m+1)→K) : List K :=
  WeightedStack.trace (F.coefficients gamma rho target) (List.ofFn (fun i=>(F.weight m i,y i))) 0 ++
    (F.totalDenominator m).trace (F.coefficients gamma rho target)

theorem reference_run (m : ℕ) (y : Fin (m+1)→K) :
    run (F.coefficients gamma rho target) (C.reference m) (List.ofFn y)=some
      ([(resultPair gamma rho target m y).1,(resultPair gamma rho target m y).2],
        trace gamma rho target m y) := by
  have hw := WeightedStack.run_code (F.coefficients gamma rho target)
    (List.ofFn (fun i=>(F.weight m i,y i))) 0 []
  simp only [List.map_ofFn,Function.comp_def,List.append_nil] at hw
  rw [weighted_numerator] at hw
  simp only [C.reference,run_append]
  simp only [run,step,bind,Option.bind_some,pure,List.nil_append]
  simp only [hw,Option.bind_some,RingFormula.run_code,F.eval_totalDenominator]
  simp [run,step,trace,resultPair,List.append_assoc]

def budget (m Y : ℕ) : ℕ := (m+1)*(Y+F.weightSize m+1)

variable {D : Type} [Fintype D] [Algebra ℚ K] {n : ℕ}
variable (presentation : FixedField K n) (base : D→Fin n→ℚ)
variable (unit : D) (hunit : presentation.decode (base unit)=1)

include unit hunit in
theorem trace_bound
    (hlit : ∀a,ArithmeticSize.Bound (fun d=>presentation.decode (base d)) 1
      (F.coefficients gamma rho target a))
    (m Y : ℕ) (y : Fin (m+1)→K)
    (hy : ∀i,ArithmeticSize.Bound (fun d=>presentation.decode (base d)) Y (y i)) :
    ∀x∈trace gamma rho target m y,
      ArithmeticSize.Bound (fun d=>presentation.decode (base d)) (budget m Y) x := by
  have hw := B.weighted_bound (F.coefficients gamma rho target)
    (fun d=>presentation.decode (base d)) unit hunit hlit
    (List.ofFn (fun i=>(F.weight m i,y i))) Y (F.weightSize m) 0 0
    (by intro p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp; exact F.weight_size m i)
    (by intro p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp; exact hy i)
    (ArithmeticSize.Bound.zero unit 0)
  have hd := B.formula_bound (F.coefficients gamma rho target)
    (fun d=>presentation.decode (base d)) unit hunit hlit (F.totalDenominator m)
  have hsize : (F.totalDenominator m).size≤budget m Y := by
    have h := F.totalDenominator_size m
    unfold budget
    nlinarith
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · simpa [budget] using hw.2 x hx
  · exact (hd.2 x hx).mono unit hunit hsize


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationPostprocess
end
