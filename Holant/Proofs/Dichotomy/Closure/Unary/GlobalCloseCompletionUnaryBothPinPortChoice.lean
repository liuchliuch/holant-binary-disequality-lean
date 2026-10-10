import Holant.Proofs.Closure.ClosureStableFactorPorts
import Holant.Dihedral.CompatibleClosure.PairOrder

/-! A physical outside equality loop can always use two equal mask bits.
The original selected binary ports remain fixed; only outside ports move. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinPortChoice
open Holant Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false

 theorem equal_pair {n : ℕ} (mask : Fin n→Bool) (large : 3≤n) :
    ∃i j : Fin n,i≠j ∧ mask i=mask j := by
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let c : Fin n := ⟨2,by omega⟩
  have ab : a≠b := by intro h;have hv:=congrArg Fin.val h;change 0=1 at hv;omega
  have ac : a≠c := by intro h;have hv:=congrArg Fin.val h;change 0=2 at hv;omega
  have bc : b≠c := by intro h;have hv:=congrArg Fin.val h;change 1=2 at hv;omega
  by_cases h : mask a=mask b
  · exact ⟨a,b,ab,h⟩
  by_cases k : mask a=mask c
  · exact ⟨a,c,ac,k⟩
  refine ⟨b,c,bc,?_⟩
  cases ha : mask a <;> cases hb : mask b <;> cases hc : mask c <;> simp_all

 theorem order {t : ℕ} (positive : 0<t) (mask : Fin (t+4)→Bool) :
    ∃e : Equiv.Perm (Fin (t+4)),e 0=0 ∧ e 1=1 ∧ mask (e 2)=mask (e 3) := by
  obtain ⟨i,j,different,same⟩ := equal_pair (fun i : Fin (t+2)=>mask i.succ.succ) (by omega)
  let p := Holant.Dihedral.CompatibleClosure.pairOrder i j
  let e := ClosureStableFactor.liftResidual p
  refine ⟨e,rfl,rfl,?_⟩
  change mask ((p 0).succ.succ)=mask ((p 1).succ.succ)
  rw [Holant.Dihedral.CompatibleClosure.pairOrder_first i j different,
    Holant.Dihedral.CompatibleClosure.pairOrder_second]
  exact same


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinPortChoice
end
