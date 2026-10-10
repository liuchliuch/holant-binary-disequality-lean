import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalMergeGraphs
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin

/-! Ordinary labelled pinning for the actual LocalAffine rank descent. The
remaining ports keep their order, and the pin is a retained physical vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalPinGraphs
open Holant Holant.Tractable
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (tensor contract tensor_denote contract_denote)
export NoXLocalMergeGraphs (cast cast_denote)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s k : ℕ} {arity : ℕ→ℕ}
variable {H : (j : Fin s)→Signature K (arity j.val)}
variable (N : M.Macro H (k+1)) (P : M.Macro H 1)

def pinFirst : M.Macro H k :=
  (M.cast (P.tensor N) (by omega : 1+(k+1)=k+2)).contract

variable (bit : Bool) (pin : P.network.denote=fun x=>if x 0=bit then 1 else 0)
include pin in
theorem pinFirst_value (x : Fin k→Bool) : (pinFirst N P).network.denote x=N.network.denote (Fin.cons bit x) := by
  have eval (t : Bool) :
      (M.cast (P.tensor N) (by omega : 1+(k+1)=k+2)).network.denote ((Fin.cons t (Fin.cons t x)) : Fin (k+2)→Bool)=
      (if t=bit then 1 else 0)*N.network.denote (Fin.cons t x) := by
    rw [M.cast_denote,M.tensor_denote,pin]
    simp only [Signature.tensor_apply]
    have right : (fun i : Fin (k+1)=>((Fin.cons t (Fin.cons t x)) : Fin (k+2)→Bool)
        (Fin.cast (by omega : 1+(k+1)=k+2) (Fin.natAdd 1 i)))=Fin.cons t x := by
      funext i
      have hi : Fin.cast (by omega : 1+(k+1)=k+2) (Fin.natAdd 1 i)=i.succ := by
        apply Fin.ext
        simp only [Fin.val_cast,Fin.val_natAdd,Fin.val_succ]
        omega
      rw [hi]
      rfl
    rw [right]
    rfl
  rw [pinFirst,M.contract_denote,eval,eval]
  cases bit <;> simp

def output {n : ℕ} (N : M.Macro H n) : NoXOrdinaryGraphAdjoin.Output H n where
  network := N.network
  labels := N.labels
  exact := N.exact
  ordinary := N.edges

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalPinGraphs
end
