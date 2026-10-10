import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoCapWords
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoLoop

/-! Actual two-corner rows of nonzero signed charge modulo four reduce to
arity one, two or three. Opposite signs use native X; uniform signs use a
four-edge pure-Eq4 cap. Both nonzero coefficients and the charge are tracked. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoReduce
open Holant Holant.Complexity
namespace W
export NoIPureChargeTwoWords (row)
end W
namespace C
export NoIPureChargeTwoCapWords (append_const value charge_mod)
end C
namespace R
export NoIPureChargeTwoLoop (order output value charge)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {size : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin size)→Signature K (arity i.val))

structure Reduced (residue : ℤ) where
  arity : ℕ
  positive : 0<arity
  small : arity≤3
  graph : NativeAntiTargetSource.Output H arity
  mask : Fin arity→Bool
  left : K
  right : K
  left_nonzero : left≠0
  right_nonzero : right≠0
  form : graph.network.denote=W.row mask left right
  charge : Holant.charge mask%4=residue

variable (Q : NativeAntiTargetSource.Output H 4) (p q : K) (pn : p≠0) (qn : q≠0)
variable (qform : Q.network.denote=NoIPureEqualityCap.pure p q)
include pn qn qform in
theorem exists_reduced : ∀n : ℕ,∀N : NativeAntiTargetSource.Output H n,
    ∀mask : Fin n→Bool,∀u v : K,u≠0→v≠0→N.network.denote=W.row mask u v→
    Holant.charge mask%4≠0→Nonempty (Reduced H (Holant.charge mask%4)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih=>
    intro N mask u v un vn form nonzero
    by_cases small : n≤3
    · have positive : 0<n := by
        by_contra bad
        have hn : n=0:=by omega
        subst n
        simp [Holant.charge] at nonzero
      exact ⟨⟨n,positive,small,N,mask,u,v,un,vn,form,rfl⟩⟩
    by_cases same : ∃b : Bool,mask=(fun _=>b)
    · obtain ⟨b,rfl⟩:=same
      obtain ⟨m,rfl⟩ : ∃m,n=m+4:=⟨n-4,by omega⟩
      have positive : 0<m := by
        by_contra bad
        have hm : m=0:=by omega
        subst m
        cases b <;> simp [Holant.charge,Holant.weight] at nonzero
      let V:=NoIPureChargeTwoCap.cap H N Q
      let u':=(if b then p else q)*u
      let v':=(if b then q else p)*v
      have un' : u'≠0:=mul_ne_zero (by cases b <;> assumption) un
      have vn' : v'≠0:=mul_ne_zero (by cases b <;> assumption) vn
      have value : V.network.denote=W.row (fun _ : Fin m=>b) u' v' := by
        apply C.value H positive N Q b (fun _=>b) u v p q
        · simpa only [C.append_const] using form
        · exact qform
      have charge : Holant.charge (fun _ : Fin m=>b)%4=Holant.charge (fun _ : Fin (m+4)=>b)%4 := by
        simpa only [C.append_const] using (C.charge_mod b (fun _ : Fin m=>b)).symm
      obtain ⟨D⟩:=ih m (by omega) V (fun _=>b) u' v' un' vn' value (by rwa [charge])
      exact ⟨charge ▸ D⟩
    · obtain ⟨m,rfl⟩ : ∃m,n=m+2:=⟨n-2,by omega⟩
      obtain ⟨b,e,t,ordered⟩:=R.order mask same
      let V:=R.output H N e
      have value : V.network.denote=W.row t u v:=R.value H (by omega) N mask u v form b e t ordered
      have charge : Holant.charge t%4=Holant.charge mask%4:=congrArg (fun z : ℤ=>z%4) (R.charge mask b e t ordered)
      obtain ⟨D⟩:=ih m (by omega) V t u v un vn value (by rwa [charge])
      exact ⟨charge ▸ D⟩

def produce {n : ℕ} (N : NativeAntiTargetSource.Output H n) (mask : Fin n→Bool)
    (u v : K) (un : u≠0) (vn : v≠0) (form : N.network.denote=W.row mask u v)
    (nonzero : Holant.charge mask%4≠0) : Reduced H (Holant.charge mask%4) :=
  (exists_reduced H Q p q pn qn qform n N mask u v un vn form nonzero).some

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoReduce
end
