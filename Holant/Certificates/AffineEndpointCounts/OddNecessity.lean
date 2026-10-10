import Holant.Certificates.FourthRootOdd.PhaseWitness
import Holant.Certificates.AffineEndpoint.PhaseUniqueness

/-! The odd-coset phase test characterizes the actual affine predicate. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

def oddDirection (y : Fin 3 → Bool) : Fin 4 → Bool :=
  ![y 0,y 1,y 2,y 0 ^^ y 1 ^^ y 2]

theorem oddChart_xor : ∀ y z : Fin 3 → Bool,
    oddChart (xor y z)=xor (oddChart y) (oddDirection z) := by decide +kernel

theorem oddChart_holds : ∀ y : Fin 3 → Bool, oddSystem.Holds (oddChart y) := by decide +kernel

theorem chart_thirdDifference (Q : QuadraticPhase 4) (c : ZMod 4)
    (z u v w : Fin 3 → Bool) :
    thirdDifference (fun y => c+Q.eval (oddChart y)) z u v w=0 := by
  rw [thirdDifference_add,thirdDifference_const,zero_add]
  have h := quadratic_thirdDifference Q (oddChart z)
    (oddDirection u) (oddDirection v) (oddDirection w)
  simpa only [thirdDifference,oddChart_xor] using h

theorem origin_vec3 : origin 3=![false,false,false] := by decide +kernel

theorem xor_vec3 (a b c A B C : Bool) :
    AffinePhase.xor ![a,b,c] ![A,B,C]=![a ^^ A,b ^^ B,c ^^ C] := by
  funext i
  fin_cases i <;> rfl

theorem phaseCriterion_of_thirdDifference (φ : (Fin 3 → Bool) → ZMod 4)
    (h : ∀ z u v w,thirdDifference φ z u v w=0) : PhaseCriterion φ := by
  constructor
  · intro i j hij
    have ht := h origin3 (unit3 i) (unit3 i) (unit3 j)
    have hev : ∀ a : ZMod 4,a+a=0 → a=0 ∨ a=2 := by decide +kernel
    apply hev
    fin_cases i <;> fin_cases j <;> simp at hij
    all_goals simp [thirdDifference,xor_vec3,origin_vec3,origin3,phaseMixed] at ht ⊢
    all_goals linear_combination -ht
  · have ht := h origin3 (unit3 0) (unit3 1) (unit3 2)
    simp [thirdDifference,xor_vec3,origin3,phaseMixed,phaseLinear] at ht ⊢
    linear_combination ht

theorem shiftedOdd_phaseTest_of_affine (s : State) (δ : Fin 4)
    (h : Affine (shiftedOdd s δ)) : phaseTest s δ := by
  have hv (y : Fin 3 → Bool) : shiftedOdd s δ (oddChart y)=fourthRootPhase (chartPhase s δ y) := by
    simp [shiftedOdd,oddChart_holds,chartPhase]
  have hn (y : Fin 3 → Bool) : shiftedOdd s δ (oddChart y)≠0 := by
    rw [hv]
    exact fourthRootPhase_ne_zero _
  rcases h with hz | ⟨a,ha,S,Q,hf⟩
  · exact False.elim (hn origin3 (by rw [hz]; rfl))
  have hS (y : Fin 3 → Bool) : S.Holds (oddChart y) := by
    by_contra he
    exact hn y (by rw [hf]; simp [affineFormula,he])
  have he (y : Fin 3 → Bool) : fourthRootPhase (chartPhase s δ y)=a*fourthRootPhase (Q.eval (oddChart y)) := by
    rw [←hv,hf]
    simp [affineFormula,hS]
  let c := chartPhase s δ origin3-Q.eval (oddChart origin3)
  have hc : fourthRootPhase c=a := by
    rw [fourthRootPhase_sub,he origin3]
    exact mul_div_cancel_right₀ _ (fourthRootPhase_ne_zero _)
  have hp : chartPhase s δ=(fun y => c+Q.eval (oddChart y)) := by
    funext y
    apply Holant.Certificates.AffineEndpoint.fourthRootPhase_injective
    rw [fourthRootPhase_add,hc,he]
  unfold phaseTest
  rw [hp]
  exact phaseCriterion_of_thirdDifference _ (chart_thirdDifference Q c)

theorem shiftedOdd_affine_iff_phaseTest (s : State) (δ : Fin 4) :
    Affine (shiftedOdd s δ) ↔ phaseTest s δ :=
  ⟨shiftedOdd_phaseTest_of_affine s δ,shiftedOdd_affine s δ⟩

end
end Holant.Certificates.AffineEndpointCounts
