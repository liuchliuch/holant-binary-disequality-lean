import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalRankOneSource

/-! Necessary pair identities when no actual even bad block exists. Every
failed identity is already discharged by a literal weighted rank-one source.
An origin-supported row consequently has one common fourth power and even
oriented support differences, with no support-rank restriction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginPairConditions
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open scoped BigOperators
namespace R
export NoXLocalRankOneSource (evenBad_of_even_failure evenBad_of_odd)
end R
namespace W
export NoXWeightedRankOneCore (negativeCount)
export NoXLocalRankOneWeighted (weighted_equation negativeSign_pow)
export NoXLocalRankOneCriterion (negativeSign)
end W
namespace D
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end D
namespace U
export OrdinaryNegativeXUniversalResource (EvenBad)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ}
theorem negative_origin (x : Word n) : W.negativeCount (origin n) x=0 := by
  unfold W.negativeCount
  apply Finset.sum_eq_zero
  intro i _
  simp [OrdinaryNegativeRankOneCore.neg,AffinePhase.origin]

variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (i : Fin s)→Signature K (b i.val)) (j antiLabel p0 p1 : Fin s)
variable (v w : K)
variable (ha_lit : (⟨b antiLabel.val,H antiLabel⟩ : AnySignature K)=⟨2,NoXWeightedAntiSigned.anti v w⟩)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin true⟩)
variable (hv : v≠0) (hw : w≠0) (fourth : (v : AlgebraicComplex)^4= -((w : AlgebraicComplex)^4))
variable (noBad : ¬U.EvenBad H)
variable (x y : Word (b j.val)) (hx : H j x≠0) (hy : H j y≠0)

include hv hw fourth ha_lit h0 h1 noBad hx hy in
theorem distance_even : Even (D.distance x y) := by
  rcases Nat.even_or_odd (D.distance x y) with even|odd
  · exact even
  · apply False.elim
    apply noBad
    apply R.evenBad_of_odd H j antiLabel p0 p1 v w ha_lit h0 h1 x y hv hw hx hy odd
    intro equal
    have hn : (w : AlgebraicComplex)^4≠0 := pow_ne_zero 4 (fun h=>hw (Subtype.ext h))
    apply hn
    linear_combination (1/2 : AlgebraicComplex)*(equal.symm.trans fourth)

include hv hw fourth ha_lit h0 h1 noBad hx hy in
theorem weighted_equal : ((w : AlgebraicComplex)^W.negativeCount x y*(H j x : AlgebraicComplex))^4=
    ((v : AlgebraicComplex)^W.negativeCount x y*(H j y : AlgebraicComplex))^4 := by
  by_contra failure
  exact noBad (R.evenBad_of_even_failure H j antiLabel p0 p1 v w ha_lit h0 h1 x y hv hw hx hy
    (distance_even H j antiLabel p0 p1 v w ha_lit h0 h1 hv hw fourth noBad x y hx hy) failure)

variable (atOrigin : H j (origin (b j.val))≠0)
include hv hw fourth ha_lit h0 h1 noBad atOrigin hy in
theorem fourth_origin : (H j (origin (b j.val)) : AlgebraicComplex)^4=(H j y : AlgebraicComplex)^4 := by
  have he := weighted_equal H j antiLabel p0 p1 v w ha_lit h0 h1 hv hw fourth noBad
    (origin (b j.val)) y atOrigin hy
  simpa only [negative_origin,pow_zero,one_mul] using he

include hv hw fourth ha_lit h0 h1 noBad atOrigin hx hy in
theorem fourth_equal : (H j x : AlgebraicComplex)^4=(H j y : AlgebraicComplex)^4 :=
  (fourth_origin H j antiLabel p0 p1 v w ha_lit h0 h1 hv hw fourth noBad x hx atOrigin).symm.trans
    (fourth_origin H j antiLabel p0 p1 v w ha_lit h0 h1 hv hw fourth noBad y hy atOrigin)

include hv hw fourth ha_lit h0 h1 noBad atOrigin hx hy in
theorem negative_even : Even (W.negativeCount x y) := by
  have he := (W.weighted_equation (v : AlgebraicComplex) (w : AlgebraicComplex)
    (fun h=>hw (Subtype.ext h)) fourth x y (H j x : AlgebraicComplex) (H j y : AlgebraicComplex)).mp
    (weighted_equal H j antiLabel p0 p1 v w ha_lit h0 h1 hv hw fourth noBad x y hx hy)
  have common:=fourth_equal H j antiLabel p0 p1 v w ha_lit h0 h1 hv hw fourth noBad x y hx hy atOrigin
  rw [common] at he
  have sign : W.negativeSign x y=1 :=
    mul_right_cancel₀ (pow_ne_zero 4 (fun h=>hy (Subtype.ext h))) (by simpa only [one_mul] using he.symm)
  have power : (-1 : AlgebraicComplex)^W.negativeCount x y=1 := by
    rw [←W.negativeSign_pow]
    exact sign
  rcases Nat.even_or_odd (W.negativeCount x y) with even|odd
  · exact even
  · rw [odd.neg_one_pow] at power
    norm_num at power


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginPairConditions
end
