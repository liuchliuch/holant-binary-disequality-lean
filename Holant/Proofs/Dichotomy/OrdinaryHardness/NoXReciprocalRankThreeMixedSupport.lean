import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeMixedSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeUniformMixedSource

/-! Full shifted simplex support, with the real projection scalar retained,
for both actual pin-only rank-three mixed resources. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeMixedSupport
open Holant Holant.Tractable
namespace P
export OrdinaryNegativeSparseRankThreePorts (port)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
export NoXGeneralMixedOrientation (sign)
export NoXReciprocalMixedProjectionCore (logical)
export OrdinaryNegativeSparseMixingAlpha (codeSeven)
end P
namespace A
export NoXReciprocalRankThreeMixedSource (resource ambient_value present)
end A
namespace U
export NoXReciprocalRankThreeUniformMixedSource (resource ambient_value present)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)

private theorem code_free (x : Fin 3→Bool) :
    (![P.codeSeven x 0,P.codeSeven x 1,P.codeSeven x 2] : Fin 3→Bool)=x := by
  funext i
  fin_cases i <;> rfl
private theorem exists_code (z : Fin 7→Bool) :
    z=P.codeSeven ![z 0,z 1,z 2] ↔ ∃x : Fin 3→Bool,z=P.codeSeven x := by
  constructor
  · intro h
    exact ⟨_,h⟩
  · rintro ⟨x,rfl⟩
    rw [code_free]

section Ordinary
variable (W : OrdinaryNegativeSparseMinimalRank.PinWitness (H j) 3)
variable (total : ∀q,Odd (P.bundleSize (P.port W.chart) q))
theorem ordinary (z : Fin 7→Bool) : (A.resource H j p0 p1 h0 h1 W total).ambient H z≠0 ↔
    ∃x : Fin 3→Bool,P.logical (P.sign (P.port W.chart)) z=P.codeSeven x := by
  rw [A.ambient_value,mul_ne_zero_iff]
  have scalar : (NoXReciprocalMixedProjectionSum.scale (K:=K) (P.port W.chart) (P.sign (P.port W.chart)) : AlgebraicComplex)≠0 :=
    fun h=>NoXReciprocalMixedProjectionSum.scale_ne_zero (K:=K) _ _ (Subtype.ext h)
  rw [and_iff_right scalar,OrdinaryNegativeSparseRankThreeSupport.support_iff W.chart (A.present H j W total),exists_code]
end Ordinary

section Uniform
variable (W : OrdinaryNegativeSparseUniformMinimal.UniformPinWitness (H j) 3)
variable (total : ∀q,Odd (P.bundleSize (P.port W.chart) q))
theorem uniform (z : Fin 7→Bool) : (U.resource H j p0 p1 h0 h1 W total).ambient H z≠0 ↔
    ∃x : Fin 3→Bool,P.logical (P.sign (P.port W.chart)) z=P.codeSeven x := by
  rw [U.ambient_value,mul_ne_zero_iff]
  have scalar : (NoXReciprocalMixedProjectionSum.scale (K:=K) (P.port W.chart) (P.sign (P.port W.chart)) : AlgebraicComplex)≠0 :=
    fun h=>NoXReciprocalMixedProjectionSum.scale_ne_zero (K:=K) _ _ (Subtype.ext h)
  rw [and_iff_right scalar,OrdinaryNegativeSparseRankThreeSupport.support_iff W.chart (U.present H j W total),exists_code]
end Uniform


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeMixedSupport
end
