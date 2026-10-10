import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2FlatDescent
import Holant.ReedMuller.FlatNetwork.Tensor

/-! Zero and nullary rows cannot be genuine nonflat counterexamples. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2FlatNonzero
open Holant Holant.LocalDrafts.MainChain
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.AffineRadon
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false

theorem nullary (f : Signature ℂ 0) : FlatOrZero f := by
  classical
  let c := f Fin.elim0
  by_cases hc : c=0
  · left
    funext x
    exact (congrArg f (Subsingleton.elim x Fin.elim0)).trans hc
  · right
    have h := flat_nonzero_smul (Signature.scalar 1) nullary_unit_flat c hc
    convert h using 1
    funext x
    change f x=c*1
    rw [mul_one]
    exact congrArg f (Subsingleton.elim x Fin.elim0)

variable {K : Type*} [Field K] {n : ℕ} (phi : K→+*ℂ) (f : Signature K n)
variable (bad : ¬FlatOrZero (RingHomRealization.mapSignature phi f))

include bad in
theorem positive : 0<n := by
  cases n with
  | zero => exact False.elim (bad (nullary _))
  | succ n => exact Nat.succ_pos n

include bad in
theorem nonzero : f≠0 := by
  intro zero
  apply bad
  left
  funext x
  simp [RingHomRealization.mapSignature,zero]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2FlatNonzero
end
