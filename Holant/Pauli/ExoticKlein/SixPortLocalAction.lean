import Holant.Pauli.ExoticKlein.SixPortPhysicalCards

/-! Actual one-port matrix actions for physical normalization. Composition and
invertibility retain the exact exotic fusion scalars. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators
variable {P : Type*} [DecidableEq P]

 def localMatrix (p : P) (A : Mat) (h : Tensor ℂ P) : Tensor ℂ P :=
  fun x => ∑ u : Bool, A (x p) u*h (Function.update x p u)

 def localAction (p : P) (a : Label) (h : Tensor ℂ P) : Tensor ℂ P := localMatrix p (E a) h

 theorem localMatrix_zero (p : P) (A : Mat) : localMatrix p A (0 : Tensor ℂ P) = 0 := by
  funext x
  simp [localMatrix]

 theorem localMatrix_equality (p : P) (h : Tensor ℂ P) : localMatrix p Signature.equality h = h := by
  funext x
  simp [localMatrix,Signature.equality]

 theorem localMatrix_scale_matrix (p : P) (s : ℂ) (A : Mat) (h : Tensor ℂ P) :
    localMatrix p (scale s A) h = fun x => s*localMatrix p A h x := by
  funext x
  simp only [localMatrix,scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

 theorem localMatrix_scale_tensor (p : P) (s : ℂ) (A : Mat) (h : Tensor ℂ P) :
    localMatrix p A (fun x => s*h x) = fun x => s*localMatrix p A h x := by
  funext x
  simp only [localMatrix,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

 theorem localMatrix_comp (p : P) (A B : Mat) (h : Tensor ℂ P) :
    localMatrix p A (localMatrix p B h) = localMatrix p (Kernel.mul A B) h := by
  funext x
  simp only [localMatrix,Fintype.sum_bool,Function.update_self,Function.update_idem,Kernel.mul_apply]
  ring

 theorem localAction_twice (p : P) (a : Label) (h : Tensor ℂ P) :
    localAction p a (localAction p a h) = fun x => omega a a*h x := by
  unfold localAction
  rw [localMatrix_comp,fusion,label_add_self,localMatrix_scale_matrix]
  have hzero : E 0 = (Signature.equality : Mat) := by funext x y; exact E_zero x y
  rw [hzero,localMatrix_equality]

 theorem localAction_injective (p : P) (a : Label) : Function.Injective (localAction p a) := by
  intro h g he
  have hh := congrArg (localAction p a) he
  rw [localAction_twice,localAction_twice] at hh
  funext x
  exact mul_left_cancel₀ (omega_ne_zero a a) (congrFun hh x)

 theorem localAction_ne_zero (p : P) (a : Label) (h : Tensor ℂ P) (hn : h ≠ 0) : localAction p a h ≠ 0 := by
  intro hz
  apply hn
  apply localAction_injective p a
  rw [hz]
  exact (localMatrix_zero p (E a)).symm

 theorem localAction_inverse (p : P) (a : Label) (h : Tensor ℂ P) :
    localAction p a (fun x => (omega a a)⁻¹*localAction p a h x) = h := by
  unfold localAction
  rw [localMatrix_scale_tensor]
  change (fun x => (omega a a)⁻¹*localAction p a (localAction p a h) x) = h
  rw [localAction_twice]
  funext x
  rw [← mul_assoc,inv_mul_cancel₀ (omega_ne_zero a a),one_mul]

end
end Holant.Pauli.ExoticKlein.SixPort
