import Holant.ReedMuller.CoefficientAtlas.Coefficients
import Holant.BoundaryAction

namespace Holant.ReedMuller.CoefficientAtlas
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

def walshKernel (a b : Bool) : ℂ := if a && b then -1 else 1

theorem walshKernel_sign (a b : Bool) :
    walshKernel a b=(sign (G := ℂˣ) (-1) (boolValue a*boolValue b):ℂ) := by
  cases a <;> cases b <;> simp [walshKernel,sign,boolValue]

theorem prod_walshKernel (x y : Point → Bool) :
    (∏ p, walshKernel (x p) (y p))=(sign (G := ℂˣ) (-1) (dot (vector x) (vector y)):ℂ) := by
  have H := sign_sum (G := ℂˣ) (-1) (by simp) Finset.univ
    (fun p : Point => boolValue (x p)*boolValue (y p))
  have HC := congrArg (fun u : ℂˣ => (u:ℂ)) H
  simpa only [walshKernel_sign,Units.coe_prod,dot,vector] using HC.symm

theorem dot_add_right (x y z : BinaryVector 8) : dot x (y+z)=dot x y+dot x z := by
  simp [dot,mul_add,Finset.sum_add_distrib]

theorem evaluate_add (a b : Param) : evaluate (a+b)=evaluate a+evaluate b := evaluation.map_add a b

/-- Character cancellation is proved by an actual translation of the finite
parameter group; it is not an assumed Fourier-transform identity. -/
theorem complex_fourier_sum (x : BinaryVector 8) :
    (∑ a : Param, (sign (G := ℂˣ) (-1) (dot x (evaluate a)):ℂ))=
      if ∃ a : Param, evaluate a=x then 16 else 0 := by
  classical
  by_cases hx : ∃ a : Param, evaluate a=x
  · have hmem : x∈code := hx
    have hz (a : Param) : dot x (evaluate a)=0 := (code_selfDual x).mp hmem _ ⟨a,rfl⟩
    simp [hx,hz,sign,Fintype.card_fun]
  · simp only [hx,ite_false]
    have hb : ∃ b : Param, dot x (evaluate b)≠0 := by
      by_contra hn
      push_neg at hn
      apply hx
      apply (code_selfDual x).mpr
      intro y hy
      obtain ⟨a,rfl⟩ := hy
      exact hn a
    obtain ⟨b,hb⟩ := hb
    let F : Param → ℂ := fun a => (sign (G := ℂˣ) (-1) (dot x (evaluate a)):ℂ)
    have HF (a : Param) : F (a+b)= -F a := by
      dsimp only [F]
      rw [evaluate_add,dot_add_right,sign_add (G := ℂˣ) (-1) (by simp)]
      simp [sign,hb]
    have H := Equiv.sum_comp (Equiv.addRight b) F
    change (∑ a : Param,F (a+b))=∑ a : Param,F a at H
    simp only [HF,Finset.sum_neg_distrib] at H
    have H2 : (2:ℂ)*(∑ a : Param,F a)=0 := by linear_combination -H
    exact (mul_eq_zero.mp H2).resolve_left (by norm_num)


end
end Holant.ReedMuller.CoefficientAtlas
