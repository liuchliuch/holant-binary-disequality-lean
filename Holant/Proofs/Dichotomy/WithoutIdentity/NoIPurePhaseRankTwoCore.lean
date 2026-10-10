import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureClosedMinimal
import Holant.Proofs.Hardness.EOBinaryPlaneAffine

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoSource
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {f : Signature AlgebraicComplex n}

theorem faces_fourth (D : SystematicSupport f 2)
    (faces : ∀i : Fin 2,∀z : Word 2,Affine (minor D {i} z)) :
    Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification.CommonFourth D.reduced := by
  intro x
  apply Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionFullSupport.constant_of_coordinates
    2 (fun z=>D.reduced z^4) _ x ![false,false]
  intro i z
  have ha:=face_affine_of_minor D {i} z (faces i z)
  have value (b : Bool) : OrdinaryNegativeAffineThreeFaces.face D.reduced {i} z
      (Function.update z i b)=D.reduced (Function.update z i b) := by
    apply ite_eq_left
    intro j hj
    have hji:j≠i:=by simpa using hj
    simp [Function.update,hji]
  have h0:OrdinaryNegativeAffineThreeFaces.face D.reduced {i} z (Function.update z i false)≠0:=by
    rw [value];exact D.reduced_full _
  have h1:OrdinaryNegativeAffineThreeFaces.face D.reduced {i} z (Function.update z i true)≠0:=by
    rw [value];exact D.reduced_full _
  simpa only [value] using ha.fourth_power_eq _ _ h0 h1

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoSource
end
