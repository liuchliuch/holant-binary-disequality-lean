import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoOppositeSupply

/-! In the separately odd uniform residual, even total multiplicity removes
only a proved semantic Affine gauge. The output is an unchanged-label
opposite alpha resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoUniformOpposite
open Holant Holant.Tractable
open OrdinaryNegativeSparseRankDescent
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness)
export OrdinaryNegativeSparseMinimalRank (row)
export NoXSeparateSignedProjection (signedCount)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end P
namespace Q
export OrdinaryNegativeRankTwoPorts (port word_code)
export OrdinaryNegativeRankTwoSupport (essential)
end Q
namespace U
export OrdinaryNegativeRankTwoUniformSource (chart chart_minimal nonzero)
export OrdinaryNegativeAffineRankOne (uniform uniform_square)
end U
namespace R
export NoXGeneralMixingResources (OppositeAlpha)
export NoXGeneralRankTwoLocal (resource compressed)
export NoXOppositeMixingLift (opposite)
end R
namespace G
export OrdinaryNegativeSignedRowsUniform (gauge gauge_inverse_affine gauge_ne_zero)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : P.UniformPinWitness (H j) 2)
variable (both : ∀q bit,Odd (P.signedCount (Q.port W.chart) q bit))
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (U.uniform (minor W.chart S z)))

theorem twisted_value (z : Fin 3→Bool) : Q.essential (U.chart W) z=
    G.gauge (Q.port W.chart) z*Q.essential W.chart z := by
  simp only [Q.essential,U.chart,OrdinaryNegativeSparseUniformMinimal.supportChart,
    U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,
    G.gauge,OrdinaryNegativeSignedRowsUniform.phase,OrdinaryNegativeSignedRowsUniform.read,
    OrdinaryNegativeSignedPortsCore.word]
  rfl

include both square minimal in
theorem alpha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (Q.essential W.chart)) := by
  have even:=NoXGeneralRankTwoUniformLocal.even W both
  have present : 0<P.bundleSize (Q.port (U.chart W)) 2 := by
    change 0<P.bundleSize (Q.port W.chart) 2
    rw [←NoXLocalEvenCharacterPhase.totalCount,Fintype.sum_bool]
    obtain ⟨k,hk⟩:=both 2 false
    omega
  have ha:=OrdinaryNegativeRankTwoAlphaLift.alpha_of_minimal (U.chart W) present
    (U.uniform_square _ (W.square square)) (U.nonzero W) W.bad (U.chart_minimal W minimal)
  rw [OrdinaryNegativeSparseMixingAlpha.twist_action] at ha ⊢
  have good:=(G.gauge_inverse_affine (Q.port W.chart) even).mul ha
  convert good using 1
  funext z
  rw [twisted_value]
  field_simp [G.gauge_ne_zero (Q.port W.chart) z]

def resource : R.OppositeAlpha H .three where
  toOddResource:=R.resource H j p0 p1 h0 h1 W.pins W.pure (Q.port W.chart) both
  alpha:=by
    change Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
      (fun x : Fin 3→Bool=>(R.resource H j p0 p1 h0 h1 W.pins W.pure (Q.port W.chart) both).ambient H (R.opposite x)))
    have he : (fun x=>(R.resource H j p0 p1 h0 h1 W.pins W.pure (Q.port W.chart) both).ambient H (R.opposite x))=
        Q.essential W.chart := by
      funext x
      exact NoXSeparateSignedPins.ambient_value (Q.port W.chart) H j p0 p1 h0 h1 W.pins W.pure both x
    rw [he]
    exact alpha H j W both square minimal
  full:=by
    intro x
    change (R.resource H j p0 p1 h0 h1 W.pins W.pure (Q.port W.chart) both).ambient H
      (NoXWeightedAntiOppositeCap.embedding .three x)≠0
    rw [R.compressed,Q.word_code]
    exact W.chart.supported x

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoUniformOpposite
end
