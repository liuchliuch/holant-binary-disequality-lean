import Holant.Proofs.Hardness.BinaryThreeSupportStarProgrammeCompiler
import Holant.Proofs.BinaryInterpolation.PostprocessBounds

/-! Every actual scalar produced by the signed-star stack programme has a
structural arithmetic-height bound, including copied/erased operands and all
intermediate common-denominator products. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarProgramme
open Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open Holant.Algebraic
open scoped BigOperators
namespace B
export Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds (formula_bound weighted_bound)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

variable {K : Type} [Field K]

def resultPair (m : ℕ) (y : Fin (m+1)→K) : K×K :=
  ((-1 : K)^m * commonNumerator (BinaryThreeSupportStarCommon.divisor (K:=K) (m:=m))
      (fun i=>y i*BinaryThreeSupportStarCommon.numerator i),
    commonDenominator (BinaryThreeSupportStarCommon.divisor (K:=K) (m:=m)))
def trace (m : ℕ) (y : Fin (m+1)→K) : List K :=
  WeightedStack.trace coefficients (List.ofFn (fun i=>(weight m i,y i))) 0 ++
    (totalDenominator m).trace coefficients

theorem weighted_numerator (m : ℕ) (y : Fin (m+1)→K) :
    WeightedStack.value coefficients (List.ofFn (fun i=>(weight m i,y i))) 0=(resultPair m y).1 := by
  rw [WeightedStack.value_eq_sum]
  simp only [zero_add,List.map_ofFn,Function.comp_def,List.sum_ofFn,eval_weight,resultPair,
    commonNumerator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem reference_run (m : ℕ) (y : Fin (m+1)→K) :
    run coefficients (reference m) (List.ofFn y)=
      some ([(resultPair m y).1,(resultPair m y).2],trace m y) := by
  have hw := WeightedStack.run_code coefficients (List.ofFn (fun i=>(weight m i,y i))) 0 []
  simp only [List.map_ofFn,Function.comp_def,List.append_nil] at hw
  rw [weighted_numerator] at hw
  simp only [reference,run_append]
  simp only [run,step,bind,Option.bind_some,pure,List.nil_append]
  simp only [hw,Option.bind_some,RingFormula.run_code,eval_totalDenominator]
  simp [run,step,trace,resultPair,List.append_assoc]

def budget (m Y : ℕ) : ℕ := (m+1)*(Y+weightSize m+1)

variable {D : Type} [Algebra ℚ K] [Fintype D] {n : ℕ}
variable (F : FixedField K n) (base : D→Fin n→ℚ) (unit : D) (hunit : F.decode (base unit)=1)

include unit hunit in
theorem trace_bound (hlit : ∀a,ArithmeticSize.Bound (fun d=>F.decode (base d)) 1
    (coefficients (K:=K) a)) (m Y : ℕ) (y : Fin (m+1)→K)
    (hy : ∀i,ArithmeticSize.Bound (fun d=>F.decode (base d)) Y (y i)) :
    ∀x∈trace m y,ArithmeticSize.Bound (fun d=>F.decode (base d)) (budget m Y) x := by
  have hw := B.weighted_bound coefficients (fun d=>F.decode (base d)) unit hunit hlit
    (List.ofFn (fun i=>(weight m i,y i))) Y (weightSize m) 0 0
    (by intro p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp; exact weight_size m i)
    (by intro p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp; exact hy i)
    (ArithmeticSize.Bound.zero unit 0)
  have hd := B.formula_bound coefficients (fun d=>F.decode (base d)) unit hunit hlit (totalDenominator m)
  have hsize : (totalDenominator m).size≤budget m Y := by
    have h := totalDenominator_size m
    unfold budget
    nlinarith
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · simpa [budget] using hw.2 x hx
  · exact (hd.2 x hx).mono unit hunit hsize

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarProgramme
