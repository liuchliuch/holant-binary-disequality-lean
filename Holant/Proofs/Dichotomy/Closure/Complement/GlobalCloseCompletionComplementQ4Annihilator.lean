import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-! Recover a distinguished exponential coefficient from positive samples.
Only separation from the desired node is required. Undesired nodes may
coincide arbitrarily; their repeated factors cause no division by zero. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Annihilator
open scoped BigOperators
open Polynomial
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K ι : Type} [Field K] [Fintype ι]

def annihilator (nodes : ι→K) : Polynomial K:=∏i, (X-C (nodes i))
def moment (p : Polynomial K) (samples : ℕ→K) : K:=
  ∑k∈Finset.range (p.natDegree+1),p.coeff k*samples (k+1)

theorem degree (nodes : ι→K) : (annihilator nodes).natDegree=Fintype.card ι := by
  classical
  rw [annihilator,Polynomial.natDegree_prod_of_monic]
  · simp
  · intro i _
    exact monic_X_sub_C (nodes i)

theorem evaluation (nodes : ι→K) (x : K) :
    (annihilator nodes).eval x=∏i,(x-nodes i) := by
  classical
  rw [annihilator,Polynomial.eval_prod]
  simp

theorem root (nodes : ι→K) (i : ι) : (annihilator nodes).eval (nodes i)=0 := by
  classical
  rw [evaluation]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

theorem nonzero (nodes : ι→K) (target : K) (separate : ∀i,target≠nodes i) :
    (annihilator nodes).eval target≠0 := by
  classical
  rw [evaluation]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>sub_ne_zero.mpr (separate i))

theorem moment_sum (p : Polynomial K) (nodes coefficients : ι→K) :
    moment p (fun k=>∑i,coefficients i*nodes i^k)=
      ∑i,coefficients i*nodes i*p.eval (nodes i) := by
  classical
  unfold moment
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.eval_eq_sum_range]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ]
  ring

theorem moment_single (p : Polynomial K) (node coefficient : K) :
    moment p (fun k=>coefficient*node^k)=coefficient*node*p.eval node := by
  unfold moment
  rw [Polynomial.eval_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change p.coeff k*(coefficient*node^(k+1))=coefficient*node*(p.coeff k*node^k)
  rw [pow_succ]
  ring

theorem moment_add (p : Polynomial K) (f g : ℕ→K) :
    moment p (fun k=>f k+g k)=moment p f+moment p g := by
  simp [moment,mul_add,Finset.sum_add_distrib]

theorem isolate (nodes coefficients : ι→K) (target answer : K) :
    moment (annihilator nodes) (fun k=>answer*target^k+∑i,coefficients i*nodes i^k)=
      answer*target*(annihilator nodes).eval target := by
  rw [moment_add,moment_single,moment_sum]
  simp_rw [root,mul_zero]
  simp

theorem recover (nodes coefficients : ι→K) (target answer : K)
    (targetNonzero : target≠0) (separate : ∀i,target≠nodes i) :
    moment (annihilator nodes) (fun k=>answer*target^k+∑i,coefficients i*nodes i^k) /
      (target*∏i,(target-nodes i))=answer := by
  rw [isolate,←evaluation]
  rw [mul_assoc,mul_div_cancel_right₀ _ (mul_ne_zero targetNonzero (nonzero nodes target separate))]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Annihilator
end
