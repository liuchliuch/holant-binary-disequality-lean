import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOneSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseUniformMinimal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsPins

/-! Rank-one minimal witnesses become actual original-label even bad blocks
or literal odd-interface unary resources. Pure pins preserve the exact Hamming
incidence. Uniform rejection is tested semantically; no octic gate is added. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOneMinimal
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseMinimalRank
open OrdinaryNegativeSparseUniformMinimal
open scoped BigOperators
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace D
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end D
namespace A
export OrdinaryNegativeAffineRankOne.SystematicSupport
  (left right left_supported right_supported affine_iff_fourth even_uniform_iff odd_affine_or_uniform)
end A
namespace R
export OrdinaryNegativeRankOneSource (blocks balanced row row_value row_nonaffine boundary_count away_even)
end R
namespace U
export OrdinaryNegativeXUniversalResource (OddResource AlphaResource AffineResource EvenBad)
end U
namespace C
export OrdinaryNegativeOcticCommonBasis (basis action phase)
end C
namespace Q
export GlobalCloseCompletionProductAncestorAffine (unary_of_equal_fourth_powers)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem distance_pure {n m : ℕ} (p : Fin n→Bool ⊕ Fin m) (hp : PurePins p)
    (x y : Fin m→Bool) : D.distance (T.substitute p x) (T.substitute p y)=D.distance x y := by
  unfold D.distance
  calc
    _=∑i : Fin n,Sum.elim (fun _=>0) (fun j=>if x j=y j then 0 else 1) (p i) := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : p i <;> simp [T.substitute,h]
    _=_ := OrdinaryNegativeSignedRowsPins.sum_pure p hp _

variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (b i.val)) (j xLabel p0 p1 : Fin s)
variable (hx : (⟨b xLabel.val,H xLabel⟩ : AnySignature K)=⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin true⟩)
variable (x y : Fin (b j.val)→Bool)

abbrev blocks := R.blocks H j xLabel p0 p1 hx h0 h1 x y
abbrev value := R.row H j xLabel p0 p1 hx h0 h1 x y

def evenBlock (hd : Even (D.distance x y)) :
    OrdinaryNegativeSparseMixingSource.Block (s:=s) (b:=b) 1 :=
  ⟨b j.val,blocks H j xLabel p0 p1 hx h0 h1 x y,R.balanced H j xLabel p0 p1 hx h0 h1 x y hd⟩

def oddResource (hd : Odd (D.distance x y)) : U.OddResource (s:=s) b 1 where
  privateCount := b j.val
  rows := blocks H j xLabel p0 p1 hx h0 h1 x y
  constant_even q := R.away_even H j xLabel p0 p1 hx h0 h1 x y (.inl q) (by simp)
  boundary_odd i := by
    have hi : i=0 := Fin.eq_zero i
    subst i
    change Odd ((OrdinaryNegativeMixedBlockData.ports (R.blocks H j xLabel p0 p1 hx h0 h1 x y) 0).count (Sum.inr 0))
    rw [R.boundary_count]
    exact hd
  private_even i := R.away_even H j xLabel p0 p1 hx h0 h1 x y (.inr (Fin.natAdd 1 i))
    (by simp [Fin.ext_iff])

def unary (a c : AlgebraicComplex) : Signature AlgebraicComplex 1 := fun z=>if z 0 then c else a

theorem ambient_eq :
    (fun z=>(value H j xLabel p0 p1 hx h0 h1 x y z : AlgebraicComplex))=
      unary (H j x : AlgebraicComplex) (H j y : AlgebraicComplex) := by
  funext z
  simp only [value,R.row_value]
  cases hz : z 0 <;> simp [unary,hz]

theorem unary_affine (a c : AlgebraicComplex) (ha : a≠0) (he : a^4=c^4) : Affine (unary a c) :=
  Q.unary_of_equal_fourth_powers 0 a c ha he

theorem unary_alpha (a c : AlgebraicComplex) (ha : a≠0) (he : a^4= -(c^4)) :
    Affine ((C.basis true).symm.action (unary a c)) := by
  have h : a^4=(zetaEight*c)^4 := by rw [mul_pow,zetaEight_pow_four];simpa
  convert unary_affine a (zetaEight*c) ha h using 1
  funext z
  rw [C.action]
  cases hz : z 0 <;> simp [unary,C.phase,hz]

theorem ambient_full (hd : Odd (D.distance x y)) (hl : H j x≠0) (hr : H j y≠0) :
    ∀z,(oddResource H j xLabel p0 p1 hx h0 h1 x y hd).ambient H z≠0 := by
  intro z
  change (value H j xLabel p0 p1 hx h0 h1 x y z : AlgebraicComplex)≠0
  simp only [value,R.row_value]
  cases z 0
  · exact fun h=>hl (Subtype.ext h)
  · exact fun h=>hr (Subtype.ext h)

private theorem fourth_choice (f : Signature K (b j.val))
    (square : Affine (fun z=>(f z : AlgebraicComplex)^2))
    (hl : f x≠0) (hr : f y≠0) :
    (f x : AlgebraicComplex)^4=(f y : AlgebraicComplex)^4 ∨
    (f x : AlgebraicComplex)^4= -((f y : AlgebraicComplex)^4) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  simpa only [←pow_mul] using OrdinaryNegativeAffineSquareSupport.eighth_equal
    (fun z=>(f z : AlgebraicComplex)) square x y
    (fun h=>hl (Subtype.ext h)) (fun h=>hr (Subtype.ext h))

section Ordinary
variable (W : PinWitness (H j) 1)
variable (square : Affine (fun z=>(H j z : AlgebraicComplex)^2))

def leftWord := T.substitute W.pins (A.left W.chart)
def rightWord := T.substitute W.pins (A.right W.chart)

theorem left_nonzero : H j (leftWord H j W)≠0 :=
  fun h=>(A.left_supported W.chart) (congrArg Subtype.val h)
theorem right_nonzero : H j (rightWord H j W)≠0 :=
  fun h=>(A.right_supported W.chart) (congrArg Subtype.val h)

include square in
theorem fourth_bad : (H j (leftWord H j W) : AlgebraicComplex)^4≠
    (H j (rightWord H j W) : AlgebraicComplex)^4 := by
  intro he
  exact W.bad ((A.affine_iff_fourth W.chart (W.square square)).mpr he)

include W square hx h0 h1 in
theorem ordinary_supply : U.EvenBad H ∨ Nonempty (U.AlphaResource H .one) := by
  let x:=leftWord H j W
  let y:=rightWord H j W
  have hl : H j x≠0 := left_nonzero H j W
  have hr : H j y≠0 := right_nonzero H j W
  have bad : (H j x : AlgebraicComplex)^4≠(H j y : AlgebraicComplex)^4 := fourth_bad H j W square
  rcases Nat.even_or_odd (D.distance x y) with even|odd
  · refine Or.inl ⟨1,evenBlock H j xLabel p0 p1 hx h0 h1 x y even,?_⟩
    exact R.row_nonaffine H j xLabel p0 p1 hx h0 h1 x y K.subtype hl hr bad
  · have phase := (fourth_choice j x y (H j) square hl hr).resolve_left bad
    refine Or.inr ⟨{
      toOddResource := oddResource H j xLabel p0 p1 hx h0 h1 x y odd
      alpha := ?_
      full := ambient_full H j xLabel p0 p1 hx h0 h1 x y odd hl hr }⟩
    change Affine ((C.basis true).symm.action (fun z=>(value H j xLabel p0 p1 hx h0 h1 x y z : AlgebraicComplex)))
    rw [ambient_eq]
    exact unary_alpha _ _ (fun h=>hl (Subtype.ext h)) phase
end Ordinary

section Uniform
variable (W : UniformPinWitness (H j) 1)
variable (square : Affine (fun z=>(H j z : AlgebraicComplex)^2))

def uniformLeft := T.substitute W.pins (A.left W.chart)
def uniformRight := T.substitute W.pins (A.right W.chart)

theorem uniform_left_nonzero : H j (uniformLeft H j W)≠0 :=
  fun h=>(A.left_supported W.chart) (congrArg Subtype.val h)
theorem uniform_right_nonzero : H j (uniformRight H j W)≠0 :=
  fun h=>(A.right_supported W.chart) (congrArg Subtype.val h)

include W square hx h0 h1 in
theorem uniform_supply : U.EvenBad H ∨ Nonempty (U.AffineResource H .one) := by
  let x:=uniformLeft H j W
  let y:=uniformRight H j W
  have hl : H j x≠0 := uniform_left_nonzero H j W
  have hr : H j y≠0 := uniform_right_nonzero H j W
  have dist : D.distance x y=D.distance (A.left W.chart) (A.right W.chart) := distance_pure W.pins W.pure _ _
  rcases Nat.even_or_odd (D.distance x y) with even|odd
  · have em : Even (D.distance (A.left W.chart) (A.right W.chart)) := dist ▸ even
    have bad : ¬Affine (row (H j) W.pins) := fun h=>W.bad ((A.even_uniform_iff W.chart (W.square square) em).mpr h)
    have diff : (H j x : AlgebraicComplex)^4≠(H j y : AlgebraicComplex)^4 :=
      fun he=>bad ((A.affine_iff_fourth W.chart (W.square square)).mpr he)
    exact Or.inl ⟨1,evenBlock H j xLabel p0 p1 hx h0 h1 x y even,
      R.row_nonaffine H j xLabel p0 p1 hx h0 h1 x y K.subtype hl hr diff⟩
  · have om : Odd (D.distance (A.left W.chart) (A.right W.chart)) := dist ▸ odd
    have affine := (A.odd_affine_or_uniform W.chart (W.square square) om).resolve_right W.bad
    have equal : (H j x : AlgebraicComplex)^4=(H j y : AlgebraicComplex)^4 :=
      (A.affine_iff_fourth W.chart (W.square square)).mp affine
    refine Or.inr ⟨{
      toOddResource := oddResource H j xLabel p0 p1 hx h0 h1 x y odd
      affine := ?_
      full := ambient_full H j xLabel p0 p1 hx h0 h1 x y odd hl hr }⟩
    change Affine (fun z=>(value H j xLabel p0 p1 hx h0 h1 x y z : AlgebraicComplex))
    rw [ambient_eq]
    exact unary_affine _ _ (fun h=>hl (Subtype.ext h)) equal
end Uniform

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOneMinimal
end
