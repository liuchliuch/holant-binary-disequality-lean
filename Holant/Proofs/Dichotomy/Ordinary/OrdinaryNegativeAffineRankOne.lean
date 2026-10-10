import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSystematicSupport
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSquareReciprocal
import Holant.Proofs.Dichotomy.Closure.Product.GlobalCloseCompletionProductAncestorAffine
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionDistance

/-! Exact rank-one base of sparse regularization. The two actual supported
words and their coefficients are retained. Odd Hamming distance leaves only
Affine or the uniform eighth-root Affine twist; even distance keeps both
class tests identical. No physical compressed row is assumed here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineRankOne
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open Holant.ReedMuller.FlatNetwork
open OrdinaryNegativeAffineSystematicSupport
open scoped BigOperators
namespace R
export GlobalCloseCompletionProductAncestorAffine (unary_of_equal_fourth_powers)
end R
namespace Dst
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end Dst
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {n : ℕ}

def sign (x : Fin n→Bool) : AlgebraicComplex := ∏i,if x i then -1 else 1

theorem sign_sq (x : Fin n→Bool) : sign x^2=1 := by
  rw [sign,←Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  cases x i <;> norm_num

theorem sign_distance (x y : Fin n→Bool) : sign x*sign y=(-1 : AlgebraicComplex)^Dst.distance x y := by
  rw [sign,sign,Dst.distance,←Finset.prod_mul_distrib,←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> cases y i <;> norm_num

def uniform (f : Signature AlgebraicComplex n) : Signature AlgebraicComplex n :=
  localTwist (fun _=>true) f

theorem uniform_fourth (f : Signature AlgebraicComplex n) (x : Fin n→Bool) :
    uniform f x^4=sign x*f x^4 := by
  simp only [uniform,localTwist_apply,mul_pow,←Finset.prod_pow,Bool.true_and,sign]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp [zetaEight_pow_four]

theorem uniform_support (f : Signature AlgebraicComplex n) (x : Fin n→Bool) :
    uniform f x≠0 ↔ f x≠0 := by
  have hn : (∏i : Fin n,if x i then zetaEight else 1)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    cases x i <;> simp [zetaEight_ne_zero]
  simp only [uniform,localTwist_apply,Bool.true_and,mul_ne_zero_iff,and_iff_right hn]

theorem uniform_square (f : Signature AlgebraicComplex n) (h : Affine (fun x=>f x^2)) :
    Affine (fun x=>uniform f x^2) := by
  have hs := (OrdinaryNegativeAffineSquareReciprocal.twist_square_affine (fun _ : Fin n=>true)).mul h
  convert hs using 1
  funext x
  simp only [uniform,localTwist_apply,mul_pow,←Finset.prod_pow,Bool.true_and]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp [zetaEight_sq]

namespace SystematicSupport
variable {f : Signature AlgebraicComplex n} (D : SystematicSupport f 1)

def left : Fin n→Bool := D.encode (fun _=>false)
def right : Fin n→Bool := D.encode (fun _=>true)

@[simp] theorem left_free : (left D) (D.ports 0)=false := D.free _ _
@[simp] theorem right_free : (right D) (D.ports 0)=true := D.free _ _

theorem left_supported : f (left D)≠0 := D.supported _
theorem right_supported : f (right D)≠0 := D.supported _

theorem distinct : (left D)≠(right D) := by
  intro h
  have hh := congrFun h (D.ports 0)
  simpa only [(left_free D),(right_free D),Bool.false_eq_true] using hh

theorem supported_words (x : Fin n→Bool) (hx : f x≠0) : x=(left D) ∨ x=(right D) := by
  have he : (fun i : Fin 1=>x (D.ports i))=(fun _=>x (D.ports 0)) := by
    funext i
    fin_cases i
    rfl
  have hc := D.covers x hx
  rw [he] at hc
  cases hb : x (D.ports 0)
  · exact Or.inl (by simpa only [hb,left] using hc.symm)
  · exact Or.inr (by simpa only [hb,right] using hc.symm)

/-- At rank one the actual Affine formula is equivalent to equality of the
two nonzero fourth powers, irrespective of signs and fixed coordinates. -/
theorem affine_iff_fourth (square : Affine (fun x=>f x^2)) :
    Affine f ↔ f (left D)^4=f (right D)^4 := by
  constructor
  · intro hf
    exact hf.fourth_power_eq (left D) (right D) (left_supported D) (right_supported D)
  · intro equal
    have hn : f≠0 := by intro hz;exact (left_supported D) (congrFun hz (left D))
    obtain ⟨S,hS⟩ := OrdinaryNegativeAffineSquareSupport.exists_support_system f square hn
    have hu := R.unary_of_equal_fourth_powers (D.ports 0) (f (left D)) (f (right D))
      (left_supported D) equal
    have hr := hu.restrict S
    convert hr using 1
    funext x
    by_cases hx : f x≠0
    · rw [ite_eq_left ((hS x).mpr hx)]
      rcases (supported_words D) x hx with rfl|rfl <;> simp only [(left_free D),(right_free D),
        Bool.false_eq_true,ite_false,ite_true]
    · rw [ite_eq_right (mt (hS x).mp hx)]
      exact not_ne_iff.mp hx

def uniformChart : SystematicSupport (uniform f) 1 where
  ports := D.ports
  injective := D.injective
  encode := D.encode
  affine := D.affine
  free := D.free
  supported z := (uniform_support f _).mpr (D.supported z)
  covers x hx := D.covers x ((uniform_support f x).mp hx)

/-- The uniform octic twist is tested at the same two original words. -/
theorem uniform_iff_signed_fourth (square : Affine (fun x=>f x^2)) :
    Affine (uniform f) ↔ sign (left D)*f (left D)^4=sign (right D)*f (right D)^4 := by
  have h := affine_iff_fourth (uniformChart D) (uniform_square f square)
  simpa only [uniformChart,left,right,uniform_fourth] using h

/-- The two fourth-power tests differ only when the original support words
have odd Hamming distance, exactly the incidence parity of the physical unary. -/
theorem even_uniform_iff (square : Affine (fun x=>f x^2))
    (even : Even (Dst.distance (left D) (right D))) :
    Affine (uniform f) ↔ Affine f := by
  have equalSigns : sign (right D)=sign (left D) := by
    calc
      sign (right D)=sign (left D)^2*sign (right D) := by rw [sign_sq,one_mul]
      _=sign (left D)*(sign (left D)*sign (right D)) := by ring
      _=sign (left D) := by rw [sign_distance,even.neg_one_pow,mul_one]
  rw [(uniform_iff_signed_fourth D) square,(affine_iff_fourth D) square,equalSigns]
  have hn : sign (left D)≠0 := by
    intro hz
    have hh := sign_sq (left D)
    norm_num [hz] at hh
  exact ⟨fun h=>mul_left_cancel₀ hn h,fun h=>congrArg (fun z=>sign (left D)*z) h⟩

/-- At odd distance an affine-square rank-one row is already in one of the
two global Affine phase classes. This is a genuine base classification. -/
theorem odd_affine_or_uniform (square : Affine (fun x=>f x^2))
    (odd : Odd (Dst.distance (left D) (right D))) : Affine f ∨ Affine (uniform f) := by
  have eighth := OrdinaryNegativeAffineSquareSupport.eighth_equal f square
    (left D) (right D) (left_supported D) (right_supported D)
  have fourth : f (left D)^4=f (right D)^4 ∨ f (left D)^4=-(f (right D)^4) := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    simpa only [←pow_mul] using eighth
  rcases fourth with equal|negative
  · exact Or.inl (((affine_iff_fourth D) square).mpr equal)
  · right
    apply ((uniform_iff_signed_fourth D) square).mpr
    have oppositeSigns : sign (right D)=-(sign (left D)) := by
      calc
        sign (right D)=sign (left D)^2*sign (right D) := by rw [sign_sq,one_mul]
        _=sign (left D)*(sign (left D)*sign (right D)) := by ring
        _=-(sign (left D)) := by rw [sign_distance,odd.neg_one_pow];ring
    rw [negative,oppositeSigns]
    ring

/-- Rejecting both classes forces the even physical-incidence branch. -/
theorem even_of_two_rejections (square : Affine (fun x=>f x^2))
    (notAffine : ¬Affine f) (notUniform : ¬Affine (uniform f)) :
    Even (Dst.distance (left D) (right D)) := by
  rcases Nat.even_or_odd (Dst.distance (left D) (right D)) with even|odd
  · exact even
  · exact False.elim (((odd_affine_or_uniform D) square odd).elim notAffine notUniform)

end SystematicSupport

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineRankOne
end
