import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedRankOneSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalRankOneWeighted
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedOddUnaryCap

/-! Genuine rank-one LocalAffine rejection is discharged using the actual
weighted antidiagonal. Even distance exposes a bad unary directly; odd distance
exposes a full odd unary and the literal antidiagonal cap makes it even/bad. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalRankOneSource
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport
namespace R
export NoXWeightedRankOneSource (blocks balanced row row_value boundary_count away_even)
end R
namespace C
export OrdinaryNegativeAffineRankOne.SystematicSupport (left right left_supported right_supported)
end C
namespace U
export OrdinaryNegativeXUniversalResource (OddResource EvenBad)
end U
namespace D
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end D
namespace W
export NoXWeightedRankOneCore (negativeCount)
end W
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

def evenBlock (even : Even (D.distance x y)) : OrdinaryNegativeSparseMixingSource.Block (s:=s) (b:=b) 1 :=
  ⟨b j.val,R.blocks H j antiLabel p0 p1 v w ha_lit h0 h1 x y,
    R.balanced H j antiLabel p0 p1 v w ha_lit h0 h1 x y even⟩

variable (hv : v≠0) (hw : w≠0) (hx : H j x≠0) (hy : H j y≠0)

include hv hw hx hy in
theorem row_full (z : Fin 1→Bool) :
    (R.row (K:=K) H j antiLabel p0 p1 v w ha_lit h0 h1 x y z : AlgebraicComplex)≠0 := by
  rw [R.row_value]
  cases z 0
  · exact fun h=>mul_ne_zero (pow_ne_zero _ hw) hx (Subtype.ext h)
  · exact fun h=>mul_ne_zero (pow_ne_zero _ hv) hy (Subtype.ext h)

include hv hw hx hy ha_lit h0 h1 in
theorem evenBad_of_even_failure (even : Even (D.distance x y))
    (failure : ((w : AlgebraicComplex)^W.negativeCount x y*(H j x : AlgebraicComplex))^4≠
      ((v : AlgebraicComplex)^W.negativeCount x y*(H j y : AlgebraicComplex))^4) : U.EvenBad H := by
  refine ⟨1,evenBlock H j antiLabel p0 p1 v w ha_lit h0 h1 x y even,?_⟩
  intro affine
  have h := affine.fourth_power_eq (fun _=>false) (fun _=>true)
    (row_full H j antiLabel p0 p1 v w ha_lit h0 h1 x y hv hw hx hy _)
    (row_full H j antiLabel p0 p1 v w ha_lit h0 h1 x y hv hw hx hy _)
  apply failure
  change (R.row (K:=K) H j antiLabel p0 p1 v w ha_lit h0 h1 x y (fun _=>false) : AlgebraicComplex)^4=
    (R.row (K:=K) H j antiLabel p0 p1 v w ha_lit h0 h1 x y (fun _=>true) : AlgebraicComplex)^4 at h
  simpa only [R.row_value,Bool.false_eq_true,ite_false,ite_true,
    IntermediateField.coe_mul,IntermediateField.coe_pow] using h

include hv hw hx hy ha_lit h0 h1 in
theorem evenBad_of_odd (odd : Odd (D.distance x y))
    (gap : (v : AlgebraicComplex)^4≠(w : AlgebraicComplex)^4) : U.EvenBad H := by
  apply NoXWeightedOddUnaryCap.evenBad H antiLabel v w ha_lit
    (oddResource H j antiLabel p0 p1 v w ha_lit h0 h1 x y odd) hv hw ?_ gap
  intro z
  exact row_full H j antiLabel p0 p1 v w ha_lit h0 h1 x y hv hw hx hy z

variable (chart : SystematicSupport (fun z=>(H j z : AlgebraicComplex)) 1)
variable (square : Affine (fun z=>(H j z : AlgebraicComplex)^2))
variable (bad : ¬LocalAffine (fun z=>(H j z : AlgebraicComplex)))
variable (fourth : (v : AlgebraicComplex)^4= -((w : AlgebraicComplex)^4))

include chart hv hw ha_lit h0 h1 square bad fourth in
theorem evenBad_of_rank_one : U.EvenBad H := by
  let x:=C.left chart
  let y:=C.right chart
  have hx : H j x≠0 := fun h=>C.left_supported chart (congrArg (fun a : K=>(a : AlgebraicComplex)) h)
  have hy : H j y≠0 := fun h=>C.right_supported chart (congrArg (fun a : K=>(a : AlgebraicComplex)) h)
  rcases Nat.even_or_odd (D.distance x y) with even|odd
  · apply evenBad_of_even_failure H j antiLabel p0 p1 v w ha_lit h0 h1 x y hv hw hx hy even
    intro equal
    apply bad
    exact (NoXLocalRankOneWeighted.local_iff_even_weighted chart square
      (v : AlgebraicComplex) (w : AlgebraicComplex) (fun h=>hw (Subtype.ext h)) fourth).mpr ⟨even,equal⟩
  · apply evenBad_of_odd H j antiLabel p0 p1 v w ha_lit h0 h1 x y hv hw hx hy odd
    intro equal
    have hn : (w : AlgebraicComplex)^4≠0 := pow_ne_zero 4 (fun h=>hw (Subtype.ext h))
    have hz : (w : AlgebraicComplex)^4=0 := by linear_combination (1/2 : AlgebraicComplex)*(equal.symm.trans fourth)
    exact hn hz

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalRankOneSource
end
