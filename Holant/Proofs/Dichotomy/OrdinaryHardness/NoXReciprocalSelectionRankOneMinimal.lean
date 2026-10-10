import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOnePins
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOneMinimal

/-! The actual minimal rank-one pin witness supplies the two-point support
and nonzero anti weights internally; only its separate incidence case remains. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneMinimal
open Holant Holant.Tractable
open OrdinaryNegativeSparseMinimalRank
namespace A
export OrdinaryNegativeAffineRankOne.SystematicSupport (left right supported_words left_supported right_supported)
end A
namespace P
export NoXReciprocalSelectionRankOne (ports)
export NoXSeparateSignedProjection (signedCount)
end P
namespace R
export NoXReciprocalSelectionRankOnePins (resource anti minor)
end R
namespace U
export OrdinaryNegativeXUniversalResource (OddResource)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : PinWitness (H j) 1)
variable (odd : ∀q bit,Odd (P.signedCount (P.ports (A.left W.chart) (A.right W.chart)) q bit))
include h0 h1 odd in
theorem exists_anti : ∃R : U.OddResource (s:=s) b 2,∃v w : K,v≠0 ∧ w≠0 ∧
    R.signature H=NoXWeightedAntiSigned.anti v w := by
  let x:=A.left W.chart
  let y:=A.right W.chart
  have support : ∀z,R.minor H j W.pins z≠0→z=x ∨ z=y := by
    intro z hz
    apply A.supported_words W.chart z
    exact fun zero=>hz (Subtype.ext zero)
  refine ⟨R.resource H j p0 p1 h0 h1 W.pins W.pure x y odd,
    R.minor H j W.pins x,R.minor H j W.pins y,?_,?_,?_⟩
  · exact fun zero=>A.left_supported W.chart (congrArg Subtype.val zero)
  · exact fun zero=>A.right_supported W.chart (congrArg Subtype.val zero)
  · exact R.anti H j p0 p1 h0 h1 W.pins W.pure x y odd support

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneMinimal
end
