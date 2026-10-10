import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedOppositeFourth
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedEqualFourth

/-! Complete actual weighted-antidiagonal branch for a finite ordinary Eq4
and two-pin source. Eighth-power failure, equal fourth powers and opposite
fourth powers are all internally consumed by genuine original-oracle proofs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiComplete
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (antiLabel : Fin src.size) (v w : src.K) (hv : v≠0) (hw : w≠0)
variable (literal : (⟨src.b antiLabel.val,src.H antiLabel⟩ : AnySignature src.K)=
  ⟨2,NoXWeightedAntiSigned.anti v w⟩)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))
include hv hw literal negative in
theorem countingHard : NoXWeightedAntiResourcesOriginal.Hard G := by
  rcases NoXWeightedAntiSquares.anti_eighth_or_hard G src negative antiLabel v w hv hw literal with eighth|hard
  swap
  · exact hard
  have sq : ((v : AlgebraicComplex)^4)^2=((w : AlgebraicComplex)^4)^2 := by
    have h:=congrArg (show src.K→+*AlgebraicComplex from src.K.subtype) eighth
    rw [map_pow,map_pow] at h
    change (v : AlgebraicComplex)^8=(w : AlgebraicComplex)^8 at h
    calc
      ((v : AlgebraicComplex)^4)^2=(v : AlgebraicComplex)^8 := by ring
      _=(w : AlgebraicComplex)^8 := h
      _=((w : AlgebraicComplex)^4)^2 := by ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp sq with equal|opposite
  · exact NoXWeightedEqualFourth.countingHard G src antiLabel v w hv hw literal equal negative
  · exact NoXWeightedOppositeFourth.countingHard G src antiLabel v w hv hw literal opposite negative

include hv hw literal in
theorem tract_or_hard : Tract (GenericOrdinarySource.family G src) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_cases tract : Tract (GenericOrdinarySource.family G src)
  · exact Or.inl tract
  · exact Or.inr (countingHard G src antiLabel v w hv hw literal
      ((GenericOrdinarySource.rejected_iff G src).mp tract))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiComplete
end
