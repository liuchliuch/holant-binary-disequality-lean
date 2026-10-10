import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedRankOneSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOneMinimal

/-! Actual minimal rank-one resources with equal-fourth weighted anti gates.
The complete weight factors remain in the two unary coefficients, and the
old Affine/alpha alternatives are transported by their proved common power. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedRankOneSupply
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseMinimalRank
open OrdinaryNegativeSparseUniformMinimal
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace D
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end D
namespace C
export OrdinaryNegativeAffineRankOne.SystematicSupport
  (left right left_supported right_supported affine_iff_fourth even_uniform_iff odd_affine_or_uniform)
end C
namespace R
export NoXWeightedRankOneSource (blocks balanced row row_value boundary_count away_even)
export NoXWeightedRankOneCore (negativeCount)
end R
namespace O
export OrdinaryNegativeRankOneMinimal (unary unary_affine unary_alpha distance_pure)
end O
namespace U
export OrdinaryNegativeXUniversalResource (OddResource AlphaResource AffineResource EvenBad)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (i : Fin s)→Signature K (b i.val)) (j antiLabel p0 p1 : Fin s)
variable (v w : K)
variable (ha_lit : (⟨b antiLabel.val,H antiLabel⟩ : AnySignature K)=⟨2,NoXWeightedAntiSigned.anti v w⟩)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin true⟩)
variable (x y : Fin (b j.val)→Bool)

def evenBlock (even : Even (D.distance x y)) : OrdinaryNegativeSparseMixingSource.Block (s:=s) (b:=b) 1 :=
  ⟨b j.val,R.blocks H j antiLabel p0 p1 v w ha_lit h0 h1 x y,
    R.balanced H j antiLabel p0 p1 v w ha_lit h0 h1 x y even⟩

def oddResource (odd : Odd (D.distance x y)) : U.OddResource (s:=s) b 1 where
  privateCount := b j.val
  rows := R.blocks H j antiLabel p0 p1 v w ha_lit h0 h1 x y
  constant_even q := R.away_even H j antiLabel p0 p1 v w ha_lit h0 h1 x y (.inl q) (by simp)
  boundary_odd i := by
    have hi : i=0 := Fin.eq_zero i
    subst i
    change Odd ((OrdinaryNegativeMixedBlockData.ports
      (R.blocks H j antiLabel p0 p1 v w ha_lit h0 h1 x y) 0).count (.inr 0))
    rw [R.boundary_count]
    exact odd
  private_even i := R.away_even H j antiLabel p0 p1 v w ha_lit h0 h1 x y (.inr (Fin.natAdd 1 i))
    (by simp [Fin.ext_iff])

def leftValue : AlgebraicComplex := (w : AlgebraicComplex)^R.negativeCount x y*(H j x : AlgebraicComplex)
def rightValue : AlgebraicComplex := (v : AlgebraicComplex)^R.negativeCount x y*(H j y : AlgebraicComplex)

theorem ambient_eq :
    (fun z=>(R.row (K:=K) H j antiLabel p0 p1 v w ha_lit h0 h1 x y z : AlgebraicComplex))=
      O.unary (leftValue H j w x y) (rightValue H j v x y) := by
  funext z
  rw [R.row_value]
  cases hz : z 0 <;> simp [O.unary,leftValue,rightValue,hz]

variable (hv : v≠0) (hw : w≠0)
variable (hl : H j x≠0) (hr : H j y≠0)
include hw hl in
theorem left_nonzero : leftValue H j w x y≠0 :=
  mul_ne_zero (pow_ne_zero _ (fun h=>hw (Subtype.ext h))) (fun h=>hl (Subtype.ext h))
include hv hr in
theorem right_nonzero : rightValue H j v x y≠0 :=
  mul_ne_zero (pow_ne_zero _ (fun h=>hv (Subtype.ext h))) (fun h=>hr (Subtype.ext h))

variable (fourth : (v : AlgebraicComplex)^4=(w : AlgebraicComplex)^4)
include fourth in
theorem phase_fourth : ((v : AlgebraicComplex)^R.negativeCount x y)^4=
    ((w : AlgebraicComplex)^R.negativeCount x y)^4 := by
  rw [pow_right_comm,pow_right_comm (w : AlgebraicComplex),fourth]

include hw fourth in
theorem fourth_equal_iff : leftValue H j w x y^4=rightValue H j v x y^4 ↔
    (H j x : AlgebraicComplex)^4=(H j y : AlgebraicComplex)^4 := by
  simp only [leftValue,rightValue,mul_pow,phase_fourth j v w x y fourth]
  constructor
  · exact mul_left_cancel₀ (pow_ne_zero _ (pow_ne_zero _ (fun h=>hw (Subtype.ext h))))
  · exact congrArg _

include fourth in
theorem fourth_opposite (h : (H j x : AlgebraicComplex)^4= -((H j y : AlgebraicComplex)^4)) :
    leftValue H j w x y^4= -(rightValue H j v x y^4) := by
  simp only [leftValue,rightValue,mul_pow,phase_fourth j v w x y fourth,h,mul_neg]

include hv hw hl hr ha_lit h0 h1 fourth in
theorem evenBad (even : Even (D.distance x y))
    (bad : (H j x : AlgebraicComplex)^4≠(H j y : AlgebraicComplex)^4) : U.EvenBad H := by
  refine ⟨1,evenBlock H j antiLabel p0 p1 v w ha_lit h0 h1 x y even,?_⟩
  intro aff
  change Affine (fun z=>(R.row (K:=K) H j antiLabel p0 p1 v w ha_lit h0 h1 x y z : AlgebraicComplex)) at aff
  rw [ambient_eq] at aff
  have h := aff.fourth_power_eq (fun _=>false) (fun _=>true)
    (left_nonzero H j w x y hw hl) (right_nonzero H j v x y hv hr)
  exact bad ((fourth_equal_iff H j v w x y hw fourth).mp h)

include hv hw hl hr in
theorem ambient_full (odd : Odd (D.distance x y)) :
    ∀z,(oddResource H j antiLabel p0 p1 v w ha_lit h0 h1 x y odd).ambient H z≠0 := by
  intro z
  change (R.row (K:=K) H j antiLabel p0 p1 v w ha_lit h0 h1 x y z : AlgebraicComplex)≠0
  have he := congrFun (ambient_eq H j antiLabel p0 p1 v w ha_lit h0 h1 x y) z
  rw [he]
  cases hz : z 0
  · simpa [O.unary,hz] using left_nonzero H j w x y hw hl
  · simpa [O.unary,hz] using right_nonzero H j v x y hv hr

section Ordinary
variable (W : PinWitness (H j) 1) (square : Affine (fun z=>(H j z : AlgebraicComplex)^2))
include W hv hw fourth ha_lit h0 h1 square in
theorem ordinary_supply : U.EvenBad H ∨ Nonempty (U.AlphaResource H .one) := by
  let x:=OrdinaryNegativeRankOneMinimal.leftWord H j W
  let y:=OrdinaryNegativeRankOneMinimal.rightWord H j W
  have hl : H j x≠0 := OrdinaryNegativeRankOneMinimal.left_nonzero H j W
  have hr : H j y≠0 := OrdinaryNegativeRankOneMinimal.right_nonzero H j W
  have bad : (H j x : AlgebraicComplex)^4≠(H j y : AlgebraicComplex)^4 :=
    OrdinaryNegativeRankOneMinimal.fourth_bad H j W square
  rcases Nat.even_or_odd (D.distance x y) with even|odd
  · exact Or.inl (evenBad H j antiLabel p0 p1 v w ha_lit h0 h1 x y hv hw hl hr fourth even bad)
  · have phase : (H j x : AlgebraicComplex)^4= -((H j y : AlgebraicComplex)^4) := by
      apply (sq_eq_sq_iff_eq_or_eq_neg.mp ?_).resolve_left bad
      simpa only [←pow_mul] using OrdinaryNegativeAffineSquareSupport.eighth_equal
        (fun z=>(H j z : AlgebraicComplex)) square x y (fun h=>hl (Subtype.ext h)) (fun h=>hr (Subtype.ext h))
    refine Or.inr ⟨{
      toOddResource := oddResource H j antiLabel p0 p1 v w ha_lit h0 h1 x y odd
      alpha := ?_
      full := ambient_full H j antiLabel p0 p1 v w ha_lit h0 h1 x y hv hw hl hr odd }⟩
    change Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
      (fun z=>(R.row (K:=K) H j antiLabel p0 p1 v w ha_lit h0 h1 x y z : AlgebraicComplex)))
    rw [ambient_eq]
    exact O.unary_alpha _ _ (left_nonzero H j w x y hw hl) (fourth_opposite H j v w x y fourth phase)
end Ordinary

section Uniform
variable (W : UniformPinWitness (H j) 1) (square : Affine (fun z=>(H j z : AlgebraicComplex)^2))
include W hv hw fourth ha_lit h0 h1 square in
theorem uniform_supply : U.EvenBad H ∨ Nonempty (U.AffineResource H .one) := by
  let x:=OrdinaryNegativeRankOneMinimal.uniformLeft H j W
  let y:=OrdinaryNegativeRankOneMinimal.uniformRight H j W
  have hl : H j x≠0 := OrdinaryNegativeRankOneMinimal.uniform_left_nonzero H j W
  have hr : H j y≠0 := OrdinaryNegativeRankOneMinimal.uniform_right_nonzero H j W
  have dist : D.distance x y=D.distance (C.left W.chart) (C.right W.chart) := O.distance_pure W.pins W.pure _ _
  rcases Nat.even_or_odd (D.distance x y) with even|odd
  · have em : Even (D.distance (C.left W.chart) (C.right W.chart)) := dist ▸ even
    have bad : ¬Affine (row (H j) W.pins) := fun h=>W.bad ((C.even_uniform_iff W.chart (W.square square) em).mpr h)
    have diff : (H j x : AlgebraicComplex)^4≠(H j y : AlgebraicComplex)^4 :=
      fun he=>bad ((C.affine_iff_fourth W.chart (W.square square)).mpr he)
    exact Or.inl (evenBad H j antiLabel p0 p1 v w ha_lit h0 h1 x y hv hw hl hr fourth even diff)
  · have om : Odd (D.distance (C.left W.chart) (C.right W.chart)) := dist ▸ odd
    have affine := (C.odd_affine_or_uniform W.chart (W.square square) om).resolve_right W.bad
    have equal : (H j x : AlgebraicComplex)^4=(H j y : AlgebraicComplex)^4 :=
      (C.affine_iff_fourth W.chart (W.square square)).mp affine
    refine Or.inr ⟨{
      toOddResource := oddResource H j antiLabel p0 p1 v w ha_lit h0 h1 x y odd
      affine := ?_
      full := ambient_full H j antiLabel p0 p1 v w ha_lit h0 h1 x y hv hw hl hr odd }⟩
    change Affine (fun z=>(R.row (K:=K) H j antiLabel p0 p1 v w ha_lit h0 h1 x y z : AlgebraicComplex))
    rw [ambient_eq]
    exact O.unary_affine _ _ (left_nonzero H j w x y hw hl) ((fourth_equal_iff H j v w x y hw fourth).mpr equal)
end Uniform


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedRankOneSupply
end
