import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoSupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixingResources
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoUniformLocal

/-! The separately odd residual supplies an actual opposite alpha resource,
including the entire compressed row, all off-code zeros and original scale. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoOppositeSupply
open Holant Holant.Tractable
open OrdinaryNegativeSparseRankDescent
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseMinimalRank (PinWitness row)
export NoXSeparateSignedProjection (signedCount)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end P
namespace Q
export OrdinaryNegativeRankTwoPorts (port word_code)
export OrdinaryNegativeRankTwoSupport (essential)
end Q
namespace R
export NoXGeneralMixingResources (OppositeAlpha)
export NoXGeneralRankTwoLocal (resource compressed)
export NoXOppositeMixingLift (opposite)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : P.PinWitness (H j) 2)
variable (both : ∀q bit,Odd (P.signedCount (Q.port W.chart) q bit))
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor W.chart S z))

def ordinary : R.OppositeAlpha H .three where
  toOddResource:=R.resource H j p0 p1 h0 h1 W.pins W.pure (Q.port W.chart) both
  alpha:=by
    change Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
      (fun x : Fin 3→Bool=>(R.resource H j p0 p1 h0 h1 W.pins W.pure (Q.port W.chart) both).ambient H (R.opposite x)))
    have he : (fun x=>(R.resource H j p0 p1 h0 h1 W.pins W.pure (Q.port W.chart) both).ambient H (R.opposite x))=
        Q.essential W.chart := by
      funext x
      exact NoXSeparateSignedPins.ambient_value (Q.port W.chart) H j p0 p1 h0 h1 W.pins W.pure both x
    rw [he]
    have present : 0<P.bundleSize (Q.port W.chart) 2 := by
      rw [←NoXLocalEvenCharacterPhase.totalCount,Fintype.sum_bool]
      obtain ⟨k,hk⟩:=both 2 false
      omega
    exact OrdinaryNegativeRankTwoAlphaLift.alpha_of_minimal W.chart present
      (W.square square) W.nonzero W.bad minimal
  full:=by
    intro x
    change (R.resource H j p0 p1 h0 h1 W.pins W.pure (Q.port W.chart) both).ambient H
      (NoXWeightedAntiOppositeCap.embedding .three x)≠0
    rw [R.compressed,Q.word_code]
    exact W.chart.supported x

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoOppositeSupply
end
