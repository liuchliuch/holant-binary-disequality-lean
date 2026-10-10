import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeLocal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeUniformMixedSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixingResources

/-! Both separately odd rank-three alternatives provide real fourteen-port
opposite-Alpha resources in the unchanged table. The uniform branch removes
only the proved affine even-incidence gauge, never a physical signed edge. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeOppositeSupply
open Holant Holant.Tractable
open OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeSignedPortsCore (word)
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseRankThreePorts (port word_code)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
export NoXSeparateSignedProjection (signedCount)
end P
namespace Q
export OrdinaryNegativeSparseRankThreeSupport (essential)
export OrdinaryNegativeSparseRankThreeAlphaLift (alpha_of_minimal alpha)
export OrdinaryNegativeSparseMixingAlpha (twist twist_action codeSeven)
end Q
namespace U
export OrdinaryNegativeAffineRankOne (uniform uniform_square)
export OrdinaryNegativeSparseRankThreeUniformSource (chart port_chart)
export OrdinaryNegativeSignedRowsUniform (portFamily count_family gauge gauge_affine_iff product uniform_value)
end U
namespace R
export NoXSeparateSignedPins (resource ambient_value)
export NoXGeneralMixingResources (OppositeAlpha)
export NoXOppositeMixingLift (opposite)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)

section Ordinary
variable (W : OrdinaryNegativeSparseMinimalRank.PinWitness (H j) 3)
variable (odd : ∀q bit,Odd (P.signedCount (P.port W.chart) q bit))
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (minor W.chart S z))
include odd in
theorem present (q : Fin 7) : 0<P.bundleSize (P.port W.chart) q := by
  rw [←NoXLocalEvenCharacterPhase.totalCount,Fintype.sum_bool]
  obtain ⟨k,hk⟩:=odd q false
  omega

def ordinary : R.OppositeAlpha H .seven where
  toOddResource := R.resource (P.port W.chart) H j p0 p1 h0 h1 W.pins W.pure odd
  alpha := by
    change Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
      (fun z : Fin 7→Bool=>(R.resource (P.port W.chart) H j p0 p1 h0 h1 W.pins W.pure odd).ambient H (R.opposite z)))
    have he : (fun z=>(R.resource (P.port W.chart) H j p0 p1 h0 h1 W.pins W.pure odd).ambient H (R.opposite z))=
        Q.essential W.chart := funext (R.ambient_value (P.port W.chart) H j p0 p1 h0 h1 W.pins W.pure odd)
    rw [he]
    exact Q.alpha_of_minimal W.chart (present H j W odd) (W.square square) W.nonzero W.bad minimal
  full := by
    intro x
    change (R.resource (P.port W.chart) H j p0 p1 h0 h1 W.pins W.pure odd).ambient H
      (Fin.addCases (Q.codeSeven x) (fun i=>!(Q.codeSeven x i)))≠0
    rw [R.ambient_value]
    change OrdinaryNegativeSparseMinimalRank.row (H j) W.pins (word (P.port W.chart) (Q.codeSeven x))≠0
    rw [P.word_code]
    exact W.chart.supported x
end Ordinary

section Uniform
variable (W : OrdinaryNegativeSparseUniformMinimal.UniformPinWitness (H j) 3)
variable (odd : ∀q bit,Odd (P.signedCount (P.port W.chart) q bit))
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (U.uniform (minor W.chart S z)))
include odd in
theorem uniform_present (q : Fin 7) : 0<P.bundleSize (P.port W.chart) q := by
  rw [←NoXLocalEvenCharacterPhase.totalCount,Fintype.sum_bool]
  obtain ⟨k,hk⟩:=odd q false
  omega
include odd in
theorem uniform_even (q : Fin 7) : Even (P.bundleSize (P.port W.chart) q) := by
  rw [←NoXLocalEvenCharacterPhase.totalCount,Fintype.sum_bool]
  exact (odd q true).add_odd (odd q false)

include odd square minimal in
theorem uniform_alpha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (Q.essential W.chart)) := by
  have pres : ∀q,0<P.bundleSize (P.port (U.chart W)) q := by
    rw [U.port_chart]
    exact uniform_present H j W odd
  have ha:=Q.alpha (U.chart W) pres (U.uniform_square _ (W.square square))
    (OrdinaryNegativeRankThreeAlphaCore.uniform_minimal_phaseSeven_affine W.chart
      (W.square square) W.bad minimal)
  have hu : Affine (U.uniform (Q.essential (U.chart W))) := by
    rw [Q.twist_action] at ha
    convert ha using 1
    funext z
    simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,Q.twist]
  let ps := U.portFamily (fun _ : Fin 1=>P.port W.chart)
  have he : ∀q,Even (OrdinaryNegativeSignedRowsUniform.count ps q) := by
    intro q
    rw [U.count_family,Fin.sum_univ_one]
    exact uniform_even H j W odd q
  have hv (z : Fin 7→Bool) : U.uniform (Q.essential (U.chart W)) z=
      U.gauge ps z*U.uniform (Q.essential W.chart) z := by
    have h:=U.uniform_value (fun _ : Fin 1=>OrdinaryNegativeSparseMinimalRank.row (H j) W.pins)
      (fun _=>P.port W.chart) z
    simp only [U.product,Fin.prod_univ_one] at h
    simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,
      Q.essential,U.port_chart] at h ⊢
    rw [h]
    ring
  have hc : Affine (U.uniform (Q.essential W.chart)) := by
    apply (U.gauge_affine_iff ps he _).mp
    convert hu using 1
    exact (funext hv).symm
  rw [Q.twist_action]
  convert hc using 1
  funext z
  simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,Q.twist]

def uniform : R.OppositeAlpha H .seven where
  toOddResource := R.resource (P.port W.chart) H j p0 p1 h0 h1 W.pins W.pure odd
  alpha := by
    change Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
      (fun z : Fin 7→Bool=>(R.resource (P.port W.chart) H j p0 p1 h0 h1 W.pins W.pure odd).ambient H (R.opposite z)))
    have he : (fun z=>(R.resource (P.port W.chart) H j p0 p1 h0 h1 W.pins W.pure odd).ambient H (R.opposite z))=
        Q.essential W.chart := funext (R.ambient_value (P.port W.chart) H j p0 p1 h0 h1 W.pins W.pure odd)
    rw [he]
    exact uniform_alpha H j W odd square minimal
  full := by
    intro x
    change (R.resource (P.port W.chart) H j p0 p1 h0 h1 W.pins W.pure odd).ambient H
      (Fin.addCases (Q.codeSeven x) (fun i=>!(Q.codeSeven x i)))≠0
    rw [R.ambient_value]
    change OrdinaryNegativeSparseMinimalRank.row (H j) W.pins (word (P.port W.chart) (Q.codeSeven x))≠0
    rw [P.word_code]
    exact W.chart.supported x
end Uniform


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeOppositeSupply
end
