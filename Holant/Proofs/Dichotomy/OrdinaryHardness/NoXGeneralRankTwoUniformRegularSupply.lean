import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoScheduleValue
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSeparateRows
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSeparateParity
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoUniformSource

/-! The same separately balanced physical rank-two schedule consumes a
uniform-bad pin witness. Its semantic octic twist is canceled by the actual
even total incidences of the complete seven-row product. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoUniformRegularSupply
open Holant Holant.Tractable
open OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeSignedPortsCore (word)
namespace P
export OrdinaryNegativeSparseMinimalRank (row)
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness)
export NoXSeparateSignedProjection (signedCount)
end P
namespace Q
export OrdinaryNegativeRankTwoPorts (port)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end Q
namespace U
export OrdinaryNegativeRankTwoUniformSource (chart port_chart chart_minimal nonzero)
export OrdinaryNegativeAffineRankOne (uniform uniform_square)
export OrdinaryNegativeSignedRowsUniform (product actual_nonaffine)
end U
namespace R
export OrdinaryNegativeXUniversalResource (EvenBad)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : P.UniformPinWitness (H j) 2)
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (U.uniform (minor W.chart S z)))

include h0 h1 square minimal in
theorem uniform : R.EvenBad H ∨
    (∀q,Odd (Q.bundleSize (Q.port W.chart) q)) ∨
    (∀q bit,Odd (P.signedCount (Q.port W.chart) q bit)) := by
  rcases NoXGeneralRankTwoSchedule.choose (Q.port W.chart) with total|both|⟨i,flags,even⟩
  · exact Or.inr (Or.inl total)
  · exact Or.inr (Or.inr both)
  · left
    let ps:=NoXGeneralRankTwoSchedule.rows (Q.port W.chart) i flags
    have ht:=NoXGeneralRankTwoScheduleValue.nonaffine (U.chart W) i flags (U.chart_minimal W minimal)
      (U.uniform_square _ (W.square square)) (U.nonzero W) W.bad
    rw [U.port_chart] at ht
    have bad := U.actual_nonaffine (fun _ : Fin 7=>P.row (H j) W.pins) ps
      (NoXGeneralSeparateParity.total_even ps even) ht
    exact NoXGeneralSeparateRows.pins_evenBad H j p0 p1 h0 h1 W.pins W.pure ps even bad

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoUniformRegularSupply
end
