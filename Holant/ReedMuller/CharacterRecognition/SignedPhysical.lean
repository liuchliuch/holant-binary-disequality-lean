import Holant.ReedMuller.CharacterRecognition.CoordinateTransport
import Holant.ReedMuller.CharacterRecognition.SignedCards
import Holant.ReedMuller.AffineRadon.PhysicalBridge

/-! Both signed actual network cards transported to the ordinary true Radon
quotient coordinates, preserving the fixed graph and Bell scalars exactly. -/
noncomputable section
namespace Holant.ReedMuller.CharacterRecognition.SignedTransport
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.RadonAccess
open Holant.ReedMuller.AffineRadon
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem actualSignedRadon_eq_physical_coordinates (F : RadonAccess.RadonFrame (n+2))
    (g : Signature ℂ (n+2)) (d l : ZMod 2) :
    (fun x => actualSignedRadon F d l (fun y => g (wordVector y)) (vectorWord x))=
      affineIsometryPullback (RadonFrame.pairToOrdinary F)
        (RadonFrame.pairToOrdinary F (ones n)) (SignedRadon.RadonFrame.boundaryCard F d l g) := by
  funext x
  simp only [affineIsometryPullback,SignedRadon.RadonFrame.boundaryCard_apply,
    FlatNetwork.vector_word,actualSignedRadon_apply]
  have he : F.pairBoundaryLinearEquiv.symm
      ((RadonFrame.pairToOrdinary F).symm
        (vectorWord x-RadonFrame.pairToOrdinary F (ones n))+ones n)=
      F.ordinaryBoundaryLinearEquiv.symm (vectorWord x) := by
    rw [map_sub,LinearEquiv.symm_apply_apply,sub_add_cancel]
    change F.pairBoundaryLinearEquiv.symm
      (F.pairBoundaryLinearEquiv (F.ordinaryBoundaryLinearEquiv.symm (vectorWord x)))=_
    exact F.pairBoundaryLinearEquiv.symm_apply_apply _
  simp only [SignedRadon.RadonFrame.boundaryLift,he]
  rfl

 theorem cflat_physical_coordinates_iff (F : RadonAccess.RadonFrame (n+2))
    (g : Signature ℂ (n+2)) (d l : ZMod 2) :
    CFlat (fun x => actualSignedRadon F d l (fun y => g (wordVector y)) (vectorWord x)) ↔
      CFlat (SignedRadon.RadonFrame.boundaryCard F d l g) := by
  rw [actualSignedRadon_eq_physical_coordinates]
  exact cflat_affineIsometryPullback_iff _ (RadonFrame.pairToOrdinary_isometry F) _ _

 theorem cflat_native_network_iff_actualSignedRadon {kap : ZMod 2 → ZMod 2 → ℂ}
    (hkap : ∀d l,kap d l≠0) (F : RadonAccess.RadonFrame (n+2))
    (G : SignedRadon.ActualGraph kap F.A) (g : Signature ℂ (n+2)) (d l : ZMod 2) :
    CFlat (SignedRadon.signedNetwork F G g d l).denote ↔
      CFlat (fun x => actualSignedRadon F d l (fun y => g (wordVector y)) (vectorWord x)) := by
  rw [SignedRadon.signedNetwork_denote,cflat_smul_iff _ (mul_ne_zero G.scalar_ne (hkap d l)),
    cflat_physical_coordinates_iff]

 theorem cflat_native_network_implies_actualSignedRadon {kap : ZMod 2 → ZMod 2 → ℂ}
    (hkap : ∀d l,kap d l≠0) (F : RadonAccess.RadonFrame (n+2))
    (G : SignedRadon.ActualGraph kap F.A) (g : Signature ℂ (n+2)) (d l : ZMod 2)
    (h : CFlat (SignedRadon.signedNetwork F G g d l).denote) :
    CFlat (fun x => actualSignedRadon F d l (fun y => g (wordVector y)) (vectorWord x)) :=
  (cflat_native_network_iff_actualSignedRadon hkap F G g d l).mp h

end Holant.ReedMuller.CharacterRecognition.SignedTransport
