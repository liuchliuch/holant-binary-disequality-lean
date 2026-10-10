import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoWords
import Holant.Dihedral.CompatibleClosure.PairOrder

/-! Select and contract one opposite-sign pair with the actual native X
edge. The exact corner weights and integer charge are preserved. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoLoop
open Holant Holant.Complexity
namespace W
export NoIPureChargeTwoWords (row charge_reindex charge_loop reindex loop_row)
end W
namespace P
export Holant.Dihedral.CompatibleClosure (pairOrder pairOrder_first pairOrder_second)
end P
namespace G
export GlobalCloseCompletionComplementQ4Templates (contract reindex)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {n size : ℕ} {arity : ℕ→ℕ}

theorem order (s : Fin (n+2)→Bool) (mixed : ¬∃b,s=(fun _=>b)) :
    ∃b : Bool,∃e : Equiv.Perm (Fin (n+2)),∃t : Fin n→Bool,
      (fun i=>s (e i))=Fin.cons b (Fin.cons (!b) t) := by
  classical
  have available : ∃j : Fin (n+2),s j≠s 0 := by
    by_contra bad
    push_neg at bad
    exact mixed ⟨s 0,funext bad⟩
  obtain ⟨j,hj⟩:=available
  have distinct : (0 : Fin (n+2))≠j := by rintro rfl;exact hj rfl
  have opposite : s j= !(s 0) := by cases h0 : s 0 <;> cases h1 : s j <;> simp_all
  let e:=P.pairOrder 0 j
  refine ⟨s 0,e,(fun i=>s (e i.succ.succ)),?_⟩
  funext i
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun k=>?_) i) i
  · simp [e,P.pairOrder_first _ _ distinct]
  · change s (e 1)= !(s 0)
    simpa only [e,P.pairOrder_second] using opposite
  · rfl

theorem charge (s : Fin (n+2)→Bool) (b : Bool) (e : Equiv.Perm (Fin (n+2)))
    (t : Fin n→Bool) (form : (fun i=>s (e i))=Fin.cons b (Fin.cons (!b) t)) :
    Holant.charge t=Holant.charge s := by
  have same:=W.charge_reindex s e
  rw [form,W.charge_loop] at same
  exact same

variable (H : (i : Fin size)→Signature K (arity i.val))
def output (N : NativeAntiTargetSource.Output H (n+2)) (e : Equiv.Perm (Fin (n+2))) :
    NativeAntiTargetSource.Output H n:=G.contract H (n:=n) (G.reindex H (n:=n+2) N e.symm)

theorem value (positive : 0<n) (N : NativeAntiTargetSource.Output H (n+2))
    (s : Fin (n+2)→Bool) (u v : K) (form : N.network.denote=W.row s u v)
    (b : Bool) (e : Equiv.Perm (Fin (n+2))) (t : Fin n→Bool)
    (ordered : (fun i=>s (e i))=Fin.cons b (Fin.cons (!b) t)) :
    (output H N e).network.denote=W.row t u v := by
  change ((Holant.Complexity.BinaryInterpolation.Chains.reindex N.network e.symm).contract
    Signature.disequality).denote=_
  rw [Network.denote_contract,Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,
    form,W.reindex,ordered,W.loop_row positive]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoLoop
end
