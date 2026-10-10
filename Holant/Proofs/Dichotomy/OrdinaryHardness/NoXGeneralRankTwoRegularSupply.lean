import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoScheduleValue
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSeparateRows
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoLocal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoAlphaCore

/-! Genuine pin-only rank-two regularization. Every repaired branch produces
an original-label EvenBad resource. The only retained cases are all total
counts odd and all separate orientation counts odd. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoRegularSupply
open Holant Holant.Tractable
open OrdinaryNegativeSparseRankDescent
namespace P
export OrdinaryNegativeSparseMinimalRank (PinWitness row)
export NoXSeparateSignedProjection (signedCount)
end P
namespace Q
export OrdinaryNegativeRankTwoPorts (port)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end Q
namespace R
export OrdinaryNegativeXUniversalResource (EvenBad OddResource)
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
variable (W : P.PinWitness (H j) 2)
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor W.chart S z))

include h0 h1 square minimal in
theorem ordinary : R.EvenBad H ∨
    (∀q,Odd (Q.bundleSize (Q.port W.chart) q)) ∨
    (∀q bit,Odd (P.signedCount (Q.port W.chart) q bit)) := by
  rcases NoXGeneralRankTwoSchedule.choose (Q.port W.chart) with total|both|⟨i,flags,even⟩
  · exact Or.inr (Or.inl total)
  · exact Or.inr (Or.inr both)
  · left
    exact NoXGeneralSeparateRows.pins_evenBad H j p0 p1 h0 h1 W.pins W.pure
      (NoXGeneralRankTwoSchedule.rows (Q.port W.chart) i flags) even
      (NoXGeneralRankTwoScheduleValue.nonaffine W.chart i flags minimal (W.square square) W.nonzero W.bad)

include square minimal in
theorem local_of_both (both : ∀q bit,Odd (P.signedCount (Q.port W.chart) q bit)) :
    LocalAffine (P.row (H j) W.pins) :=
  NoXGeneralRankTwoLocal.local_affine _ W.chart (Q.port W.chart)
    (OrdinaryNegativeRankTwoPorts.word_code W.chart) both (W.square square) W.bad
    (OrdinaryNegativeRankTwoAlphaCore.minimal_commonFourth W.chart minimal)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoRegularSupply
end
