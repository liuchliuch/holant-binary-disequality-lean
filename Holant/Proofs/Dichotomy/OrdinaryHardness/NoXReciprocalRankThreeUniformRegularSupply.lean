import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeSchedule
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeUniformBundle
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSeparateRows

/-! Actual original-table uniform rank-three repair. Every nonexceptional
separate-sign pattern is repaired by the internally selected finite schedule;
the real unbounded incidences cancel the semantic octic gauge. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeUniformRegularSupply
open Holant Holant.Tractable
open OrdinaryNegativeSparseRankDescent
namespace P
export OrdinaryNegativeSparseRankThreePorts (port)
export NoXSeparateSignedProjection (signedCount)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end P
namespace U
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness)
export OrdinaryNegativeAffineRankOne (uniform)
export NoXReciprocalRankThreeUniformBundle (rows nonaffine)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : U.UniformPinWitness (H j) 3)
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (U.uniform (minor W.chart S z)))

include h0 h1 square minimal in
theorem uniform : OrdinaryNegativeXUniversalResource.EvenBad H ∨
    (∀q,Odd (P.bundleSize (P.port W.chart) q)) ∨
    (∀q bit,Odd (P.signedCount (P.port W.chart) q bit)) := by
  rcases NoXReciprocalRankThreeSchedule.choose (P.port W.chart) with total|both|⟨l,schedule,even⟩
  · exact Or.inr (Or.inl total)
  · exact Or.inr (Or.inr both)
  · left
    exact NoXGeneralSeparateRows.pins_evenBad H j p0 p1 h0 h1 W.pins W.pure (U.rows W schedule)
      even (U.nonaffine W schedule minimal square even)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeUniformRegularSupply
end
