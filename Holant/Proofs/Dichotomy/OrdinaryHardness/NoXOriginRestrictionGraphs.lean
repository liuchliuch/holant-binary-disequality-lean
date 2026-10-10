import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalPinGraphs
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalPermutation

/-! Actual zero masks and equality masks on arbitrary ordered original ports.
Pins remain as physical boundary vertices; equality uses the retained Eq4. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginRestrictionGraphs
open Holant Holant.Tractable
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (tensor reindex tensor_denote reindex_denote)
export NoXLocalMergeGraphs (cast cast_denote equalMerge equalMerge_value)
export NoXLocalPinGraphs (pinFirst pinFirst_value)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s n : ℕ} {arity : ℕ→ℕ}
variable {H : (j : Fin s)→Signature K (arity j.val)}

def pinMaskFirst (N : M.Macro H (n+1)) (P : M.Macro H 1) : M.Macro H (n+1) :=
  M.cast (P.tensor (M.pinFirst N P)) (by omega : 1+n=n+1)

theorem pinMaskFirst_value (N : M.Macro H (n+1)) (P : M.Macro H 1) (bit : Bool)
    (pin : P.network.denote=fun x=>if x 0=bit then 1 else 0) (x : Fin (n+1)→Bool) :
    (pinMaskFirst N P).network.denote x=if x 0=bit then N.network.denote x else 0 := by
  rw [pinMaskFirst,M.cast_denote,M.tensor_denote,pin]
  simp only [Signature.tensor_apply]
  have tail : (fun i : Fin n=>x (Fin.cast (by omega : 1+n=n+1) (Fin.natAdd 1 i)))=(fun i=>x i.succ) := by
    funext i
    congr 1
    apply Fin.ext
    simp only [Fin.val_cast,Fin.val_natAdd,Fin.val_succ]
    omega
  rw [tail,M.pinFirst_value N P bit pin]
  change (if x 0=bit then (1 : K) else 0)*N.network.denote (Fin.cons bit (fun i=>x i.succ))=_
  by_cases hx : x 0=bit
  · simp only [ite_eq_left hx,one_mul]
    apply congrArg N.network.denote
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact hx.symm
    · rfl
  · simp only [ite_eq_right hx,zero_mul]

def pinMask (N : M.Macro H (n+1)) (P : M.Macro H 1) (p : Fin (n+1)) : M.Macro H (n+1) :=
  (pinMaskFirst (N.reindex (Equiv.swap 0 p)) P).reindex (Equiv.swap 0 p)

theorem pinMask_value (N : M.Macro H (n+1)) (P : M.Macro H 1) (p : Fin (n+1)) (bit : Bool)
    (pin : P.network.denote=fun x=>if x 0=bit then 1 else 0) (x : Fin (n+1)→Bool) :
    (pinMask N P p).network.denote x=if x p=bit then N.network.denote x else 0 := by
  rw [pinMask,M.reindex_denote]
  simp only [Tensor.reindex_apply]
  rw [pinMaskFirst_value _ P bit pin,M.reindex_denote]
  simp only [Tensor.reindex_apply,Equiv.swap_apply_left,Equiv.swap_apply_self]

def equalMask (N : M.Macro H (n+2)) (E : M.Macro H 4) (e : Equiv.Perm (Fin (n+2))) : M.Macro H (n+2) :=
  (M.equalMerge (N.reindex e) E).reindex e.symm

theorem equalMask_value (N : M.Macro H (n+2)) (E : M.Macro H 4)
    (eq4 : E.network.denote=Holant.EightVertex.ProductAnchor.equalityFour)
    (e : Equiv.Perm (Fin (n+2))) (p q : Fin (n+2)) (hp : e p=0) (hq : e q=1)
    (x : Fin (n+2)→Bool) :
    (equalMask N E e).network.denote x=if x p=x q then N.network.denote x else 0 := by
  rw [equalMask,M.reindex_denote]
  simp only [Tensor.reindex_apply]
  rw [M.equalMerge_value _ E eq4,M.reindex_denote]
  have h0 : e.symm 0=p := (e.symm_apply_eq).mpr hp.symm
  have h1 : e.symm 1=q := (e.symm_apply_eq).mpr hq.symm
  simp only [Tensor.reindex_apply,h0,h1,Equiv.symm_apply_apply]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginRestrictionGraphs
end
