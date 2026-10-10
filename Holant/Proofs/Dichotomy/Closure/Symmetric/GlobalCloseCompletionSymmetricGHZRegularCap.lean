import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCoordinates
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

/-! The GHZ cap determinant has nonzero discriminant. On any projective
affine line of unaries, one of five fixed integer samples is simultaneously
nonsingular and has distinct characteristic roots. This finite algebraic
selection is used to remove the defective-matrix case before inversion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZRegularCap
open Holant
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def quadratic (a b c : K) : Polynomial K := C a+C b*X+C c*X^2

theorem quadratic_eval (a b c t : K) : (quadratic a b c).eval t=a+b*t+c*t^2 := by
  simp [quadratic]

theorem quadratic_coeff_zero (a b c : K) (zero : quadratic a b c=0) : a=0 ∧ b=0 ∧ c=0 := by
  have h0:=congrArg (fun p : Polynomial K=>p.coeff 0) zero
  have h1:=congrArg (fun p : Polynomial K=>p.coeff 1) zero
  have h2:=congrArg (fun p : Polynomial K=>p.coeff 2) zero
  simp [quadratic,Polynomial.coeff_C_mul] at h0 h1 h2
  exact ⟨h0,h1,h2⟩

theorem regular_polynomial_nonzero (a b c u v : K) (discriminant : b^2-4*a*c≠0) :
    quadratic a b c*quadratic (u^2-4*a) (2*u*v-4*b) (v^2-4*c)≠0 := by
  apply mul_ne_zero
  · intro zero
    obtain ⟨ha,hb,hc⟩:=quadratic_coeff_zero a b c zero
    exact discriminant (by simp [ha,hb,hc])
  · intro zero
    obtain ⟨h0,h1,h2⟩:=quadratic_coeff_zero (u^2-4*a) (2*u*v-4*b) (v^2-4*c) zero
    have h : 16*(b^2-4*a*c)=0 := by
      linear_combination -(4*b+2*u*v)*h1+4*v^2*h0+16*a*h2
    exact discriminant ((mul_eq_zero.mp h).resolve_left (by norm_num))

theorem five_regular (a b c u v : K) (discriminant : b^2-4*a*c≠0) :
    ∃i : Fin 5,a+b*(i.val:K)+c*(i.val:K)^2≠0 ∧
      (u+v*(i.val:K))^2-4*(a+b*(i.val:K)+c*(i.val:K)^2)≠0 := by
  classical
  let p:=quadratic a b c*quadratic (u^2-4*a) (2*u*v-4*b) (v^2-4*c)
  have nonzero : p≠0:=regular_polynomial_nonzero a b c u v discriminant
  have degree : p.natDegree≤4 := by dsimp [p,quadratic]; compute_degree!
  by_contra none
  apply nonzero
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f:=fun i : Fin 5=>(i.val:K))
  · intro i j h
    apply Fin.ext
    change (i.val:K)=(j.val:K) at h
    exact Nat.cast_injective h
  · intro i
    have h : ¬(a+b*(i.val:K)+c*(i.val:K)^2≠0 ∧
        (u+v*(i.val:K))^2-4*(a+b*(i.val:K)+c*(i.val:K)^2)≠0) :=
      fun good=>none ⟨i,good⟩
    have same : p.eval (i.val:K)=(a+b*(i.val:K)+c*(i.val:K)^2)*
        ((u+v*(i.val:K))^2-4*(a+b*(i.val:K)+c*(i.val:K)^2)) := by
      simp only [p,Polynomial.eval_mul,quadratic_eval]
      ring
    rw [same]
    exact not_ne_iff.mp (fun live=>h (mul_ne_zero_iff.mp live))
  · simpa only [Fintype.card_fin] using lt_of_le_of_lt degree (by decide : 4<5)

def hyperdet (a b c d : K) : K := (a*d-b*c)^2-4*(a*c-b^2)*(b*d-c^2)

theorem ghz_hyperdet (M : Kernel K) :
    hyperdet (GlobalCloseCompletionSymmetricGHZCoordinates.ghz M ![false,false,false])
      (GlobalCloseCompletionSymmetricGHZCoordinates.ghz M ![false,false,true])
      (GlobalCloseCompletionSymmetricGHZCoordinates.ghz M ![false,true,true])
      (GlobalCloseCompletionSymmetricGHZCoordinates.ghz M ![true,true,true])=
      (M false false*M true true-M false true*M true false)^6 := by
  simp [hyperdet,GlobalCloseCompletionSymmetricGHZCoordinates.ghz_value]
  ring

theorem affine_discriminant (a b c v w : K) :
    (2*a*v+b*w)^2-4*a*(a*v^2+b*v*w+c*w^2)=(b^2-4*a*c)*w^2 := by ring

theorem five_cap_parameters (a b c d v w : K) (hyper : hyperdet a b c d≠0) (transverse : w≠0) :
    ∃i : Fin 5,
      let p:=1+(i.val:K)*v
      let q:=(i.val:K)*w
      (p*a+q*b)*(p*c+q*d)-(p*b+q*c)^2≠0 ∧
        (p*(a+c)+q*(b+d))^2-4*((p*a+q*b)*(p*c+q*d)-(p*b+q*c)^2)≠0 := by
  have nonzero : (2*(a*c-b^2)*v+(a*d-b*c)*w)^2-
      4*(a*c-b^2)*((a*c-b^2)*v^2+(a*d-b*c)*v*w+(b*d-c^2)*w^2)≠0 := by
    rw [affine_discriminant]
    exact mul_ne_zero hyper (pow_ne_zero _ transverse)
  obtain ⟨i,hi,hj⟩:=five_regular (a*c-b^2) (2*(a*c-b^2)*v+(a*d-b*c)*w)
    ((a*c-b^2)*v^2+(a*d-b*c)*v*w+(b*d-c^2)*w^2) (a+c) (v*(a+c)+w*(b+d)) nonzero
  refine ⟨i,?_,?_⟩
  · convert hi using 1 <;> ring
  · convert hj using 1 <;> ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZRegularCap
end
