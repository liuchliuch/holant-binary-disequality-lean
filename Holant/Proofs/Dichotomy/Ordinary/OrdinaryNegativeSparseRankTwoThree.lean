import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseUniformMinimal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeFourthCompatibility

/-! The shared whole-family fourth-power class excludes the rank-one base.
The selected bad original-field pin row therefore has genuine rank two or
three in the same identity/uniform class, with all proper faces accepted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankTwoThree
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeSparseMinimalRank OrdinaryNegativeSparsePinTwist
open OrdinaryNegativeSparseUniformMinimal OrdinaryNegativeAffineRankOne
open OrdinaryNegativeFourthCompatibility
namespace R
export OrdinaryNegativeAffineRankOne.SystematicSupport
  (affine_iff_fourth left right left_supported right_supported)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {n m rank : ℕ}

theorem commonFourth_pin (f : Signature AlgebraicComplex n) (p : Fin n→Bool ⊕ Fin m)
    (h : CommonFourth f) : CommonFourth (fun x=>f (T.substitute p x)) :=
  fun _x _y hx hy=>h _ _ hx hy

/-- The pinned original-coordinate phase scalar cancels from fourth powers. -/
theorem commonFourth_uniform_pin (f : Signature AlgebraicComplex n)
    (p : Fin n→Bool ⊕ Fin m) (hp : PurePins p) (h : CommonFourth (uniform f)) :
    CommonFourth (uniform (fun x=>f (T.substitute p x))) := by
  intro x y hx hy
  have hx' : uniform f (T.substitute p x)≠0 :=
    (uniform_support f _).mpr ((uniform_support (fun x=>f (T.substitute p x)) x).mp hx)
  have hy' : uniform f (T.substitute p y)≠0 :=
    (uniform_support f _).mpr ((uniform_support (fun x=>f (T.substitute p x)) y).mp hy)
  have equal := h _ _ hx' hy'
  have ex := congrFun (uniform_pin f p hp) x
  have ey := congrFun (uniform_pin f p hp) y
  rw [ex,ey,mul_pow,mul_pow] at equal
  exact mul_left_cancel₀ (pow_ne_zero 4 (pinScalar_nonzero p)) equal

variable {K : IntermediateField ℚ AlgebraicComplex} {f : Signature K n}

theorem rank_at_least_two (W : PinWitness f rank)
    (square : Affine (fun x=>(f x : AlgebraicComplex)^2))
    (fourth : CommonFourth (fun x=>(f x : AlgebraicComplex))) : 2≤rank := by
  have lower : 1≤rank := OrdinaryNegativeSparseRankDescent.rank_positive W.chart
    (W.square square) W.nonzero W.bad
  by_contra h
  have hr : rank=1 := by omega
  subst rank
  have cf := commonFourth_pin (fun x=>(f x : AlgebraicComplex)) W.pins fourth
  exact W.bad ((R.affine_iff_fourth W.chart (W.square square)).mpr
    (cf (R.left W.chart) (R.right W.chart) (R.left_supported W.chart) (R.right_supported W.chart)))

theorem uniform_rank_at_least_two (W : UniformPinWitness f rank)
    (square : Affine (fun x=>(f x : AlgebraicComplex)^2))
    (fourth : CommonFourth (uniform (fun x=>(f x : AlgebraicComplex)))) : 2≤rank := by
  have lower := W.rank_positive square
  by_contra h
  have hr : rank=1 := by omega
  subst rank
  let D := supportChart W.chart (fun x=>(uniform_support (row f W.pins) x).symm)
  have cf := commonFourth_uniform_pin (fun x=>(f x : AlgebraicComplex)) W.pins W.pure fourth
  exact W.bad ((R.affine_iff_fourth D (uniform_square _ (W.square square))).mpr
    (cf (R.left D) (R.right D) (R.left_supported D) (R.right_supported D)))

/-- Concrete identity-class regularization starts at rank two or three. -/
theorem exists_minimal_two_three (f : Signature K n)
    (square : Affine (fun x=>(f x : AlgebraicComplex)^2)) (nonzero : f≠0)
    (bad : ¬Affine (fun x=>(f x : AlgebraicComplex)))
    (fourth : CommonFourth (fun x=>(f x : AlgebraicComplex))) :
    ∃rank : ℕ,(rank=2 ∨ rank=3) ∧ ∃W : PinWitness f rank,
      ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,Affine (minor W.chart S z) := by
  obtain ⟨rank,lo,hi,W,minimal⟩ := exists_minimal f square nonzero bad
  have lower := rank_at_least_two W square fourth
  exact ⟨rank,by omega,W,minimal⟩

/-- Concrete uniform-class regularization starts at rank two or three,
with the original coefficient-field row retained. -/
theorem exists_uniform_minimal_two_three (f : Signature K n)
    (square : Affine (fun x=>(f x : AlgebraicComplex)^2)) (nonzero : f≠0)
    (bad : ¬Affine (uniform (fun x=>(f x : AlgebraicComplex))))
    (fourth : CommonFourth (uniform (fun x=>(f x : AlgebraicComplex)))) :
    ∃rank : ℕ,(rank=2 ∨ rank=3) ∧ ∃W : UniformPinWitness f rank,
      ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,
        Affine (uniform (minor W.chart S z)) := by
  obtain ⟨rank,lo,hi,W,minimal⟩ := exists_minimal_uniform f square nonzero bad
  have lower := uniform_rank_at_least_two W square fourth
  exact ⟨rank,by omega,W,minimal⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankTwoThree
end
