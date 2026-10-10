import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoWords
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoCap

/-! Four equal signed coordinates are removed by an actual pure-Eq4 cap.
The two nonzero endpoint multipliers and the signed charge residue survive. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoCapWords
open Holant Holant.Complexity
namespace W
export NoIPureChargeTwoWords (row opposite different)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

theorem append_eq_iff {m : ℕ} (s x : Fin n→Bool) (t y : Fin m→Bool) :
    Fin.append s t=Fin.append x y ↔ s=x ∧ t=y := by
  constructor
  · intro h
    constructor
    · funext i;simpa using congrFun h (Fin.castAdd m i)
    · funext i;simpa using congrFun h (Fin.natAdd n i)
  · rintro ⟨rfl,rfl⟩;rfl

theorem opposite_append {m : ℕ} (s : Fin n→Bool) (t : Fin m→Bool) :
    W.opposite (Fin.append s t)=Fin.append (W.opposite s) (W.opposite t) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp [W.opposite]

theorem constant_eq (b c : Bool) : ((fun _ : Fin 4=>b)=(fun _ : Fin 4=>c)) ↔ b=c := by
  constructor
  · intro h;exact congrFun h 0
  · rintro rfl;rfl

theorem append_const (b : Bool) :
    Fin.append (fun _ : Fin n=>b) (fun _ : Fin 4=>b)=(fun _=>b) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp

theorem algebra (positive : 0<n) (b : Bool) (s : Fin n→Bool) (u v p q : K) :
    (fun x=>p*W.row (Fin.append s (fun _ : Fin 4=>b)) u v (Fin.append x (fun _=>true))+
      q*W.row (Fin.append s (fun _ : Fin 4=>b)) u v (Fin.append x (fun _=>false)))=
    W.row s ((if b then p else q)*u) ((if b then q else p)*v) := by
  funext x
  have distinct:=W.different positive s
  cases b <;> by_cases first : x=s <;> by_cases last : x=W.opposite s
  all_goals first
    | exact False.elim (distinct (first.symm.trans last))
    | simp [W.row,opposite_append,W.opposite,append_eq_iff,constant_eq,first,last,distinct,Ne.symm distinct]
  all_goals simp [NoIPureChargeTwoWords.opposite,funext_iff,Fin.forall_fin_succ]

variable {size : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin size)→Signature K (arity i.val))

theorem value (positive : 0<n) (N : NativeAntiTargetSource.Output H (n+4))
    (Q : NativeAntiTargetSource.Output H 4) (b : Bool) (s : Fin n→Bool) (u v p q : K)
    (nf : N.network.denote=W.row (Fin.append s (fun _ : Fin 4=>b)) u v)
    (qf : Q.network.denote=NoIPureEqualityCap.pure p q) :
    (NoIPureChargeTwoCap.cap H N Q).network.denote=
      W.row s ((if b then p else q)*u) ((if b then q else p)*v) := by
  rw [NoIPureChargeTwoCap.value H N Q p q qf,nf]
  exact algebra positive b s u v p q

theorem charge_append (b : Bool) (s : Fin n→Bool) :
    charge (Fin.append s (fun _ : Fin 4=>b))=charge s+(if b then 4 else -4) := by
  have weightEq : weight (Fin.append s (fun _ : Fin 4=>b))=weight s+(if b then 4 else 0) := by
    simp only [weight,Fin.sum_univ_add,Fin.append_left,Fin.append_right]
    cases b <;> simp
  unfold charge
  rw [weightEq]
  cases b <;> simp <;> ring

theorem charge_mod (b : Bool) (s : Fin n→Bool) :
    charge (Fin.append s (fun _ : Fin 4=>b))%4=charge s%4 := by
  rw [charge_append]
  cases b <;> simp <;> omega


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoCapWords
end
