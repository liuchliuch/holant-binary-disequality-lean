import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureEqualityCap
import Holant.Support

/-! Exact two-corner rows and their signed charge. These are coefficient
identities only; the separate source modules implement every cap and loop. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoWords
open Holant
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

def opposite (s : Fin n→Bool) : Fin n→Bool:=fun i=>!s i
def row (s : Fin n→Bool) (u v : K) : Signature K n:=fun x=>
  if x=s then u else if x=opposite s then v else 0

theorem different (positive : 0<n) (s : Fin n→Bool) : s≠opposite s := by
  intro h
  have hh:=congrFun h ⟨0,positive⟩
  cases hs : s ⟨0,positive⟩ <;> simp [opposite,hs] at hh

theorem left (s : Fin n→Bool) (u v : K) : row s u v s=u := by simp [row]
theorem right (positive : 0<n) (s : Fin n→Bool) (u v : K) : row s u v (opposite s)=v := by
  simp [row,Ne.symm (different positive s)]

theorem reindex (s : Fin n→Bool) (u v : K) (e : Equiv.Perm (Fin n)) :
    Tensor.reindex e.symm (row s u v)=row (fun i=>s (e i)) u v := by
  funext x
  have eqn (z : Fin n→Bool) : (fun i=>x (e.symm i))=z ↔ x=(fun i=>z (e i)) := by
    constructor
    · intro h;funext i;simpa using congrFun h (e i)
    · intro h;funext i;simpa using congrFun h (e.symm i)
  simp only [Tensor.reindex,row,eqn]
  rfl

theorem charge_reindex (s : Fin n→Bool) (e : Equiv.Perm (Fin n)) :
    charge (fun i=>s (e i))=charge s := by
  have hw : weight (fun i=>s (e i))=weight s:=Equiv.sum_comp e (fun i=>if s i then 1 else 0)
  unfold charge
  rw [hw]

theorem opposite_cons (b : Bool) (s : Fin n→Bool) :
    opposite (Fin.cons b s)=Fin.cons (!b) (opposite s) := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;> rfl

theorem loop_row (positive : 0<n) (b : Bool) (s : Fin n→Bool) (u v : K) :
    Signature.contract Signature.disequality (row (Fin.cons b (Fin.cons (!b) s)) u v)=row s u v := by
  funext x
  rw [Signature.contract_disequality]
  have distinct:=different positive s
  cases b <;> by_cases first : x=s <;> by_cases last : x=opposite s
  all_goals first
    | exact False.elim (distinct (first.symm.trans last))
    | simp [row,opposite_cons,Fin.cons_inj,first,last,Bool.not_not,distinct,Ne.symm distinct]

theorem charge_loop (b : Bool) (s : Fin n→Bool) :
    charge (Fin.cons b (Fin.cons (!b) s))=charge s := by
  cases b <;> simp only [charge,weight,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false,
    Nat.cast_add,Nat.cast_one] <;> omega


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoWords
end
