import Holant.Tractable.Affine
import Holant.Tractable.Anchor.MatrixActions
import Mathlib.Tactic

/-! The exact finite binary alternative needed after a singular dense
source: a nonsingular affine traceless symmetric binary either already is X,
or its Z sandwich is a nonzero scalar X. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularAffineBinary
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false

def matrix (x y : AlgebraicComplex) : Kernel AlgebraicComplex := fun a b => if a then (if b then -x else y) else (if b then y else x)
def z : Kernel AlgebraicComplex := fun a b => if a then (if b then -1 else 0) else (if b then 0 else 1)

theorem square_eq_of_fourth_eq (x y : AlgebraicComplex)
    (nonsingular : x^2+y^2≠0) (powers : x^4=y^4) : x^2=y^2 := by
  have product : (x^2-y^2)*(x^2+y^2)=0 := by linear_combination powers
  exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right nonsingular)

theorem square_eq_of_affine (x y : AlgebraicComplex) (hx : x≠0) (hy : y≠0)
    (nonsingular : x^2+y^2≠0) (affine : Affine (kernelSignature (matrix x y))) :
    x^2=y^2 := by
  have powers : x^4=y^4 := by
    have h := affine.fourth_power_eq ![false,false] ![false,true]
      (by simpa [kernelSignature,matrix] using hx)
      (by simpa [kernelSignature,matrix] using hy)
    simpa [kernelSignature,matrix] using h
  have product : (x^2-y^2)*(x^2+y^2)=0 := by
    linear_combination powers
  exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right nonsingular)

theorem affine_alternative (x y : AlgebraicComplex) (hy : y≠0)
    (nonsingular : x^2+y^2≠0) (affine : Affine (kernelSignature (matrix x y))) :
    x=0 ∨ x^2=y^2 := by
  by_cases hx : x=0
  · exact Or.inl hx
  · exact Or.inr (square_eq_of_affine x y hx hy nonsingular affine)

theorem zero_is_X (y : AlgebraicComplex) : matrix 0 y=fun a b=>y*Signature.disequality a b := by
  funext a b
  cases a <;> cases b <;> simp [matrix,Signature.disequality]

theorem sandwich (x y : AlgebraicComplex) (same : x^2=y^2) :
    Kernel.mul (Kernel.mul (matrix x y) z) (matrix x y)=
      fun a b=>(2*x*y)*Signature.disequality a b := by
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.mul,matrix,z,Signature.disequality]
  all_goals ring_nf
  all_goals simp only [same]
  all_goals ring

theorem sandwich_nonzero (x y : AlgebraicComplex) (hx : x≠0) (hy : y≠0) : 2*x*y≠0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) hx) hy

/-- The scalar and the branch are internally chosen from the actual affine
binary; neither the X equation nor a favourable branch is supplied. -/
theorem actual_X_alternative (x y : AlgebraicComplex) (hy : y≠0)
    (nonsingular : x^2+y^2≠0) (affine : Affine (kernelSignature (matrix x y))) :
    (∃c : AlgebraicComplex,c≠0 ∧ matrix x y=(fun a b=>c*Signature.disequality a b)) ∨
    (∃c : AlgebraicComplex,c≠0 ∧ Kernel.mul (Kernel.mul (matrix x y) z) (matrix x y)=
      (fun a b=>c*Signature.disequality a b)) := by
  by_cases hx : x=0
  · subst x
    exact Or.inl ⟨y,hy,zero_is_X y⟩
  · exact Or.inr ⟨2*x*y,sandwich_nonzero x y hx hy,
      sandwich x y (square_eq_of_affine x y hx hy nonsingular affine)⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularAffineBinary
end
