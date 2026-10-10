import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalMinimalGraph
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionClosure

/-! Smaller actual pin masks inherit LocalAffine from least-L rank.
Their supported local twists remain Affine under any affine correction map
that fixes the selected information coordinate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalMasks
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeAffineSystematicSupport
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (row row_denote)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem twisted_fixed {n r m : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
    (q : Word m→Word r) (affine : TwoTranslate.IsAffineMap q) (i : Fin r) (bit : Bool)
    (fixed : ∀x,q x i=bit) (good : LocalAffine (pinMask f (D.ports i) bit)) (a : Word m) :
    Affine (fun x=>localTwist (D.encode (q a)) f (D.encode (q x))) := by
  have supported : pinMask f (D.ports i) bit (D.encode (q a))≠0:=by
    simpa only [pinMask,D.free,fixed,ite_true] using D.supported (q a)
  have twist:=good (D.encode (q a)) supported
  rw [NoXGeneralLocalRestriction.pin_twist] at twist
  have pulled:=twist.precompose (fun x=>D.encode (q x)) (affine_map_comp _ _ D.affine affine)
  convert pulled using 1
  funext x
  simp only [pinMask,D.free,fixed,ite_true]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (src : GenericOrdinarySource.Data G)
variable {n r : ℕ} (N : M.Macro src.H (n+2))
variable (D : SystematicSupport (fun x=>(N.network.denote x : AlgebraicComplex)) (r+1))
variable (minimal : ¬NoXGeneralLocalMinimalGraph.Witness (n:=n) (H:=src.H) src.K.subtype r)

include minimal in
theorem local_masks (i : Fin (r+1)) (bit : Bool) :
    LocalAffine (pinMask (fun x=>(N.network.denote x : AlgebraicComplex)) (D.ports i) bit) := by
  let P : M.Macro src.H 1:=M.row (src.p bit) (QuaternaryUnaryAccess.pin bit) (src.hp bit)
  have pin : P.network.denote=(fun x=>if x 0=bit then 1 else 0):=by rw [M.row_denote];rfl
  let Q:=NoXOriginRestrictionGraphs.pinMask N P (D.ports i)
  have value : (fun x=>(Q.network.denote x : AlgebraicComplex))=
      pinMask (fun x=>(N.network.denote x : AlgebraicComplex)) (D.ports i) bit:=by
    funext x
    rw [NoXOriginRestrictionGraphs.pinMask_value N P (D.ports i) bit pin]
    by_cases hx : x (D.ports i)=bit <;> simp [pinMask,hx]
  have chartQ : Nonempty (SystematicSupport (fun x=>(Q.network.denote x : AlgebraicComplex)) r):=by
    rw [value]
    exact NoXOriginRestrictionSupport.pin_chart D i bit
  rw [←value]
  by_contra bad
  exact minimal ⟨Q,bad,chartQ⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalMasks
end
