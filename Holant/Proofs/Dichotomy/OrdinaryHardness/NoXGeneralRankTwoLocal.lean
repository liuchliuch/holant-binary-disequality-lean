import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalSignedMultiplicity
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalOppositeThreePhase
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedPins

/-! The separately odd rank-two case retains its real six-port resource.
Its non-Affine compressed phase is compatible with LocalAffine, and the
actual signed multiplicities transport that class back to the original row.
No opposite bundle is discarded and no anti signature is inferred. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoLocal
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
namespace M
export NoXLocalSignedMultiplicity (local_of_canonical_twists canonical_eq_opposite)
end M
namespace O
export NoXWeightedAntiOppositeCap (embedding)
end O
namespace P
export NoXSeparateSignedProjection (signedCount)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ} (f : Signature AlgebraicComplex n) (D : SystematicSupport f 2)
variable (ps : Fin n→Port 3)
variable (chart : ∀x,word ps (OrdinaryNegativeSparseMixingAlpha.codeThree x)=D.encode x)
variable (odd : ∀q bit,Odd (P.signedCount ps q bit))
variable (square : Affine (fun x=>f x^2)) (bad : ¬Affine f)
variable (common : Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification.CommonFourth D.reduced)

include chart odd square bad common in
theorem local_affine : LocalAffine f := by
  have nonzero : f≠0 := by intro zero;exact D.supported (origin 2) (congrFun zero _)
  have reducedBad := D.nonAffine_reduced square nonzero bad
  apply M.local_of_canonical_twists .three D ps chart odd square
  intro a
  have phase:=NoXLocalOppositeThreePhase.phase_affine D.reduced D.supported common reducedBad a
  change Affine (fun x : Word 2=>NoXLocalSignedMultiplicityPhase.canonical
    (OrdinaryNegativeSparseMixingAlpha.codeThree a) (OrdinaryNegativeSparseMixingAlpha.codeThree x)*D.reduced x)
  convert phase using 1
  funext x
  congr 1
  exact M.canonical_eq_opposite .three _ _

section Original
variable {K : IntermediateField ℚ AlgebraicComplex} {s N : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (pins : Fin (b j.val)→Bool ⊕ Fin N) (pure : OrdinaryNegativeSparseMinimalRank.PurePins pins)
variable (ports : Fin N→Port 3) (oddPorts : ∀q bit,Odd (P.signedCount ports q bit))

def resource : OrdinaryNegativeXUniversalResource.OddResource (s:=s) b 6 :=
  NoXSeparateSignedPins.resource ports H j p0 p1 h0 h1 pins pure oddPorts

theorem compressed (x : Word 2) :
    (resource H j p0 p1 h0 h1 pins pure ports oddPorts).ambient H (O.embedding .three x)=
      (H j (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute pins
        (word ports (OrdinaryNegativeSparseMixingAlpha.codeThree x))) : AlgebraicComplex) :=
  NoXSeparateSignedPins.ambient_value ports H j p0 p1 h0 h1 pins pure oddPorts _
end Original


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoLocal
end
