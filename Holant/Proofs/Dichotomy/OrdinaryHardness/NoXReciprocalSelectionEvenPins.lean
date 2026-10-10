import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionEvenProjection
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedPins

/-! Pure pinning does not alter the separate incidence test. Any nonaffine
signed minor passing that test yields an actual unsigned EvenBad resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionEvenPins
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port word)
namespace C
export NoXReciprocalSelectionEvenProjection (evenBad)
end C
namespace P
export OrdinaryNegativeSignedRowsPins (signedCompose word_compose)
export NoXSeparateSignedPins (signedCount_compose)
export NoXSeparateSignedProjection (signedCount)
end P
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s n m : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (pins : Fin (b j.val)→Bool ⊕ Fin n) (pure : OrdinaryNegativeSparseMinimalRank.PurePins pins)
variable (ps : Fin n→Port m) (even : ∀q bit,Even (P.signedCount ps q bit))
include h0 h1 pure even in
theorem evenBad (bad : ¬Affine (fun z=>(H j (T.substitute pins (word ps z)) : AlgebraicComplex))) :
    OrdinaryNegativeXUniversalResource.EvenBad H := by
  apply C.evenBad H j p0 p1 h0 h1 (P.signedCompose pins ps)
    (by intro q bit;rw [P.signedCount_compose pins pure];exact even q bit)
  simpa only [P.word_compose] using bad

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionEvenPins
end
