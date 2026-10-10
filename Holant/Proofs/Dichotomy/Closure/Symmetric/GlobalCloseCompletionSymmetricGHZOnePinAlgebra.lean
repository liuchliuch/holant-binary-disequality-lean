import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCapSelection

/-! Singular pin-zero repair for a symmetric GHZ tensor, entirely in its
original coefficient field. Two actual unary walks suffice to reach a
nonsingular cap unless the source is already weighted equality. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZOnePinAlgebra
open Holant Holant.Complexity.BinaryInterpolation
namespace C
export GlobalCloseCompletionSymmetricGHZCapGraph (pencil pencil_det)
end C
namespace R
export GlobalCloseCompletionSymmetricGHZRegularCap (hyperdet)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

 theorem middle_nonzero (a b c d : K) (hyper : R.hyperdet a b c d≠0)
    (singular : a*c-b^2=0) : a*d-b*c≠0 := by
  intro zero
  exact hyper (by simp [R.hyperdet,singular,zero])

 theorem weighted_of_zero (a b c d : K) (hyper : R.hyperdet a b c d≠0)
    (singular : a*c-b^2=0) (zero : b=0) : c=0 ∧ a≠0 ∧ d≠0 := by
  have middle := middle_nonzero a b c d hyper singular
  have ad : a*d≠0 := by simpa only [zero,zero_mul,sub_zero] using middle
  have an := (mul_ne_zero_iff.mp ad).1
  have dn := (mul_ne_zero_iff.mp ad).2
  have ac : a*c=0 := by simpa only [zero,zero_pow (by decide : 2≠0),sub_zero] using singular
  exact ⟨(mul_eq_zero.mp ac).resolve_left an,an,dn⟩

 theorem nonzero_of_singular (a b c d : K) (hyper : R.hyperdet a b c d≠0)
    (singular : a*c-b^2=0) (nonzero : b≠0) : a≠0 ∧ b*d-c^2≠0 := by
  have an : a≠0 := by
    intro zero
    have squared : b^2=0 := by simpa [zero] using singular
    exact (pow_ne_zero 2 nonzero) squared
  refine ⟨an,?_⟩
  intro zero
  have identity : b*(a*d-b*c)=a*(b*d-c^2)+c*(a*c-b^2) := by ring
  rw [zero,singular,mul_zero,mul_zero,add_zero] at identity
  exact (mul_ne_zero nonzero (middle_nonzero a b c d hyper singular)) identity

 theorem walk_det (a b c d : K) (singular : a*c-b^2=0) :
    Matrix.det (C.pencil a b c d a b)=(a^2+b^2)*(b*d-c^2) := by
  rw [C.pencil_det]
  linear_combination a*(a+c)*singular

 theorem exceptional (a b c d : K) (hyper : R.hyperdet a b c d≠0)
    (singular : a*c-b^2=0) (nonzero : b≠0)
    (walkZero : Matrix.det (C.pencil a b c d a b)=0) :
    c= -a ∧ C.pencil a b c d a b=(fun i j=>if i=true ∧ j=true then b*d-c^2 else 0) := by
  obtain ⟨an,dn⟩ := nonzero_of_singular a b c d hyper singular nonzero
  have isotropic : a^2+b^2=0 := by
    rw [walk_det a b c d singular] at walkZero
    exact (mul_eq_zero.mp walkZero).resolve_right dn
  have neg : c= -a := by
    have zero : a*(c+a)=0 := by linear_combination singular+isotropic
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp zero).resolve_left an)
  refine ⟨neg,?_⟩
  funext i j
  cases i <;> cases j
  · change a*a+b*b=0
    linear_combination isotropic
  · change a*b+b*c=0
    rw [neg]
    ring
  · change a*b+b*c=0
    rw [neg]
    ring
  · change a*c+b*d=b*d-c^2
    rw [neg]
    ring

 theorem last_det (a b c d : K) (nonzero : b≠0) (det : b*d-c^2≠0) :
    Matrix.det (C.pencil a b c d 0 (b*(b*d-c^2)))≠0 := by
  have identity : Matrix.det (C.pencil a b c d 0 (b*(b*d-c^2)))=(b*(b*d-c^2))^2*(b*d-c^2) := by
    rw [C.pencil_det]
    ring
  rw [identity]
  exact mul_ne_zero (pow_ne_zero 2 (mul_ne_zero nonzero det)) det


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZOnePinAlgebra
end
