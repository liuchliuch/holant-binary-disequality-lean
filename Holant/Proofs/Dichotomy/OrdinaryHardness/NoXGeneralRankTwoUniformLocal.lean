import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenUniformGauge
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalEvenCharacterPhase
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoLocal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoUniformSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoAlphaCore

/-! The separately odd uniform rank-two residual is LocalAffine for the
actual original pin minor. The semantic uniform twist is removed using the
full Affine gauge forced by its even total character multiplicities. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoUniformLocal
open Holant Holant.Tractable
open OrdinaryNegativeSparseRankDescent
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseMinimalRank (row)
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness)
export NoXSeparateSignedProjection (signedCount)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end P
namespace Q
export OrdinaryNegativeRankTwoPorts (port word_code)
export OrdinaryNegativeSparseMixingAlpha (codeThree codeThree_affine)
end Q
namespace U
export OrdinaryNegativeRankTwoUniformSource (chart chart_minimal)
export OrdinaryNegativeAffineRankOne (uniform uniform_square)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {n : ℕ} {f : Signature K n}
variable (W : P.UniformPinWitness f 2)
variable (square : Affine (fun x=>(f x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (U.uniform (minor W.chart S z)))
variable (both : ∀q bit,Odd (P.signedCount (Q.port W.chart) q bit))
include both in
theorem even (q : Fin 3) : Even (P.bundleSize (Q.port W.chart) q) := by
  rw [←NoXLocalEvenCharacterPhase.totalCount,Fintype.sum_bool]
  exact (both q true).add_odd (both q false)

include square minimal both in
theorem local_affine : LocalAffine (P.row f W.pins) := by
  have twisted:=NoXGeneralRankTwoLocal.local_affine _ (U.chart W) (Q.port W.chart)
    (Q.word_code W.chart) both (U.uniform_square _ (W.square square)) W.bad
    (OrdinaryNegativeRankTwoAlphaCore.minimal_commonFourth (U.chart W) (U.chart_minimal W minimal))
  exact (NoXGeneralEvenUniformGauge.local_iff W.chart (Q.port W.chart) Q.codeThree Q.codeThree_affine
    (Q.word_code W.chart) (even W both)).mp twisted

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoUniformLocal
end
