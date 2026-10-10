import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureMergeAttach
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureMergeRow

/-! Signed equality coefficients and the exact one-Eq4 attachment rule.
Three equal boundary signs replace one opposite sign through a native edge. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeSigned
open Holant Holant.Complexity
open scoped BigOperators
namespace A
export NoIPureMergeAttach (output output_value)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

variable [Algebra ℚ K] {s : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (arity i.val))
variable (L : NativeAntiTargetSource.Output H (n+1)) (Q : NativeAntiTargetSource.Output H 4)
theorem attach (w : Fin n→Bool) (b : Bool)
    (left : L.network.denote=row (Fin.cons (!b) w))
    (right : Q.network.denote=Holant.EightVertex.ProductAnchor.equalityFour) :
    (A.output H L Q).network.denote=row (Fin.addCases w (fun _ : Fin 3=>b)) := by
  funext x
  rw [A.output_value]
  simp_rw [left,right,row_cons,eq4_cons]
  rw [row_append]
  have indicator (P T : Prop) [Decidable P] [Decidable T] :
      (if P then (1:K) else 0)*(if T then 1 else 0)=if P ∧ T then 1 else 0 := by
    by_cases hp : P <;> by_cases ht : T <;> simp [hp,ht]
  cases b <;> simp only [Fintype.sum_bool,Signature.disequality,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,Bool.true_eq_false,not_false_eq_true,not_true_eq_false,ite_true,ite_false,
    true_and,false_and,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero,Bool.not_not,
    eq_self_iff_true]
  all_goals try simp only [ite_true,ite_false,true_and,false_and,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero]
  all_goals simp_rw [indicator]
  all_goals simp [A.leftWord,A.rightWord,NoIPureMergeAttach.leftWord,
    NoIPureMergeAttach.rightWord,add_comm]
  all_goals rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeSigned
end
