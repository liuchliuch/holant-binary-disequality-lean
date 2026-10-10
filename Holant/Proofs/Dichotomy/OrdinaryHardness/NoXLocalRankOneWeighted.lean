import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalRankOneCriterion
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedRankOneCore

/-! The exact LocalAffine rank-one condition is precisely the even-incidence
weighted-antidiagonal unary test when the antidiagonal fourth powers oppose.
All sign multiplicities refer to the original ordered support words. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalRankOneWeighted
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport
open scoped BigOperators
namespace C
export NoXLocalRankOneCriterion (maskSign maskSign_square maskSign_nonzero maskSign_pair negativeSign local_iff_fourth)
end C
namespace R
export OrdinaryNegativeAffineRankOne.SystematicSupport (left right left_supported right_supported)
end R
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
variable {n : ℕ}

theorem negativeSign_square (s t : Fin n→Bool) : C.negativeSign s t^2=1 := by
  rw [C.negativeSign,←Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  cases s i <;> cases t i <;> norm_num

theorem negativeSign_nonzero (s t : Fin n→Bool) : C.negativeSign s t≠0 := by
  intro h
  have hh := negativeSign_square s t
  simp [h] at hh

theorem negativeSign_pow (s t : Fin n→Bool) : C.negativeSign s t=(-1)^W.negativeCount s t := by
  rw [C.negativeSign,W.negativeCount,←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases hs : s i <;> cases ht : t i <;> simp [OrdinaryNegativeRankOneCore.neg,hs,ht]

theorem negativeSign_pair (s t : Fin n→Bool) :
    C.negativeSign s t*C.negativeSign t s=(-1)^D.distance s t := by
  rw [C.negativeSign,C.negativeSign,D.distance,←Finset.prod_mul_distrib,←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> cases t i <;> norm_num

theorem signs_equal_of_even (s t : Fin n→Bool) (even : Even (D.distance s t)) :
    C.negativeSign s t=C.negativeSign t s := by
  apply mul_left_cancel₀ (negativeSign_nonzero s t)
  rw [←pow_two,negativeSign_square,negativeSign_pair,even.neg_one_pow]

theorem even_of_signs_equal (s t : Fin n→Bool) (equal : C.negativeSign s t=C.negativeSign t s) :
    Even (D.distance s t) := by
  rcases Nat.even_or_odd (D.distance s t) with ev|od
  · exact ev
  · have hp := negativeSign_pair s t
    rw [←equal,←pow_two,negativeSign_square,od.neg_one_pow] at hp
    norm_num at hp

theorem mask_comm (s t : Fin n→Bool) : C.maskSign s t=C.maskSign t s := by
  unfold C.maskSign
  apply Finset.prod_congr rfl
  intro i _
  rw [Bool.and_comm]

theorem signed_equation (a b x y : AlgebraicComplex) (ha : a^2=1) :
    a*x=b*y ↔ x=(a*b)*y := by
  constructor
  · intro h
    calc
      x=a^2*x := by rw [ha,one_mul]
      _=a*(a*x) := by ring
      _=a*(b*y) := by rw [h]
      _=(a*b)*y := by ring
  · intro h
    rw [h]
    calc
      a*(a*b*y)=a^2*(b*y) := by ring
      _=b*y := by rw [ha,one_mul]

variable {f : Signature AlgebraicComplex n} (chart : SystematicSupport f 1)
variable (square : Affine (fun x=>f x^2))

include square in
theorem local_iff_even_sign : LocalAffine f ↔
    Even (D.distance (R.left chart) (R.right chart)) ∧
      f (R.left chart)^4=C.negativeSign (R.left chart) (R.right chart)*f (R.right chart)^4 := by
  rw [C.local_iff_fourth chart square]
  rw [signed_equation _ _ _ _ (C.maskSign_square _ _),C.maskSign_pair]
  rw [signed_equation _ _ _ _ (C.maskSign_square _ _)]
  have hp : C.maskSign (R.right chart) (R.left chart)*C.maskSign (R.right chart) (R.right chart)=
      C.negativeSign (R.right chart) (R.left chart) := by
    rw [mul_comm,C.maskSign_pair]
  rw [hp]
  constructor
  · rintro ⟨hl,hr⟩
    refine ⟨even_of_signs_equal _ _ ?_,hl⟩
    exact mul_right_cancel₀ (pow_ne_zero 4 (R.right_supported chart)) (hl.symm.trans hr)
  · rintro ⟨even,h⟩
    exact ⟨h,(signs_equal_of_even _ _ even) ▸ h⟩

variable (v w : AlgebraicComplex) (hw : w≠0) (fourth : v^4= -(w^4))

include hw fourth in
theorem weighted_equation (s t : Fin n→Bool) (x y : AlgebraicComplex) :
    (w^W.negativeCount s t*x)^4=(v^W.negativeCount s t*y)^4 ↔
      x^4=C.negativeSign s t*y^4 := by
  rw [mul_pow,mul_pow,←pow_mul,←pow_mul]
  rw [Nat.mul_comm (W.negativeCount s t) 4,pow_mul,pow_mul,fourth,neg_pow,←negativeSign_pow]
  have hn : (w^4)^W.negativeCount s t≠0 := pow_ne_zero _ (pow_ne_zero _ hw)
  constructor
  · intro h
    apply mul_left_cancel₀ hn
    calc
      (w^4)^W.negativeCount s t*x^4=(C.negativeSign s t*(w^4)^W.negativeCount s t)*y^4 := h
      _=(w^4)^W.negativeCount s t*(C.negativeSign s t*y^4) := by ring
  · intro h
    rw [h]
    ring

include square hw fourth in
theorem local_iff_even_weighted : LocalAffine f ↔
    Even (D.distance (R.left chart) (R.right chart)) ∧
      (w^W.negativeCount (R.left chart) (R.right chart)*f (R.left chart))^4=
        (v^W.negativeCount (R.left chart) (R.right chart)*f (R.right chart))^4 := by
  rw [local_iff_even_sign chart square,weighted_equation v w hw fourth]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalRankOneWeighted
end
