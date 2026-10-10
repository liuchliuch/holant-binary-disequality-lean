import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalSignedMultiplicity
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalOppositeSevenPhase
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedPins

/-! The separately odd rank-three case retains its real fourteen-port resource.
Its non-Affine compressed phase is compatible with LocalAffine, and the
actual signed multiplicities transport that class back to the original row.
No opposite bundle is discarded and no anti signature is inferred. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeLocal
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
variable {n : ℕ} (f : Signature AlgebraicComplex n) (D : SystematicSupport f 3)
variable (ps : Fin n→Port 7)
variable (chart : ∀x,word ps (OrdinaryNegativeSparseMixingAlpha.codeSeven x)=D.encode x)
variable (odd : ∀q bit,Odd (P.signedCount ps q bit))
variable (square : Affine (fun x=>f x^2)) (bad : ¬Affine f)
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Word 3,
  Affine (OrdinaryNegativeSparseRankDescent.minor D S z))

include chart odd square bad minimal in
theorem local_affine : LocalAffine f := by
  have nonzero : f≠0 := by intro zero;exact D.supported (origin 3) (congrFun zero _)
  have reducedBad := D.nonAffine_reduced square nonzero bad
  apply M.local_of_canonical_twists .seven D ps chart odd square
  intro a
  have faces : ∀S : Finset (Fin 3),S.card<3→∀z : Word 3,
      Affine (OrdinaryNegativeAffineThreeFaces.face D.reduced S z) := by
    intro S hs z
    exact OrdinaryNegativeSparseRankDescent.face_affine_of_minor D S z (minimal S hs z)
  have reducedSquare : Affine (fun x=>D.reduced x^2) := square.precompose D.encode D.affine
  have phase:=NoXLocalOppositeSevenPhase.phase_affine D.reduced D.supported faces reducedSquare reducedBad a
  change Affine (fun x : Word 3=>NoXLocalSignedMultiplicityPhase.canonical
    (OrdinaryNegativeSparseMixingAlpha.codeSeven a) (OrdinaryNegativeSparseMixingAlpha.codeSeven x)*D.reduced x)
  convert phase using 1
  funext x
  congr 1
  exact M.canonical_eq_opposite .seven _ _

section Original
variable {K : IntermediateField ℚ AlgebraicComplex} {s N : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (pins : Fin (b j.val)→Bool ⊕ Fin N) (pure : OrdinaryNegativeSparseMinimalRank.PurePins pins)
variable (ports : Fin N→Port 7) (oddPorts : ∀q bit,Odd (P.signedCount ports q bit))

def resource : OrdinaryNegativeXUniversalResource.OddResource (s:=s) b 14 :=
  NoXSeparateSignedPins.resource ports H j p0 p1 h0 h1 pins pure oddPorts

theorem compressed (x : Word 3) :
    (resource H j p0 p1 h0 h1 pins pure ports oddPorts).ambient H (O.embedding .seven x)=
      (H j (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute pins
        (word ports (OrdinaryNegativeSparseMixingAlpha.codeSeven x))) : AlgebraicComplex) :=
  NoXSeparateSignedPins.ambient_value ports H j p0 p1 h0 h1 pins pure oddPorts _
end Original


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeLocal
end
