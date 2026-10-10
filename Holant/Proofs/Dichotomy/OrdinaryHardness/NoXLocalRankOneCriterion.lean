import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineRankOne

/-! Exact LocalAffine test on an actual rank-one support chart. Both supported
markings are retained. Their diagonal factors are proved from the original
ordered port bits, including opposite-bundle signs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalRankOneCriterion
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
open scoped BigOperators
namespace R
export OrdinaryNegativeAffineRankOne.SystematicSupport
  (left right left_supported right_supported supported_words affine_iff_fourth)
end R
namespace S
export OrdinaryNegativeAffineSquareReciprocal (twist_square_affine)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ}

def maskSign (alpha x : Fin n→Bool) : AlgebraicComplex :=
  ∏i,if alpha i && x i then -1 else 1

def negativeSign (x y : Fin n→Bool) : AlgebraicComplex :=
  ∏i,if x i && !(y i) then -1 else 1

theorem maskSign_square (alpha x : Fin n→Bool) : maskSign alpha x^2=1 := by
  rw [maskSign,←Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  cases alpha i <;> cases x i <;> norm_num

theorem maskSign_nonzero (alpha x : Fin n→Bool) : maskSign alpha x≠0 := by
  intro h
  have hz := maskSign_square alpha x
  simp [h] at hz

theorem maskSign_pair (x y : Fin n→Bool) :
    maskSign x x*maskSign x y=negativeSign x y := by
  rw [maskSign,maskSign,negativeSign,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> cases y i <;> norm_num

theorem twist_support (f : Signature AlgebraicComplex n) (alpha x : Fin n→Bool) :
    localTwist alpha f x≠0 ↔ f x≠0 := by
  have hn : (∏i,if alpha i && x i then zetaEight else 1)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    split_ifs <;> simp [zetaEight_ne_zero]
  simp only [localTwist_apply,mul_ne_zero_iff,and_iff_right hn]

theorem twist_fourth (f : Signature AlgebraicComplex n) (alpha x : Fin n→Bool) :
    localTwist alpha f x^4=maskSign alpha x*f x^4 := by
  simp only [localTwist_apply,mul_pow,←Finset.prod_pow,maskSign]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp [zetaEight_pow_four]

theorem twist_square (f : Signature AlgebraicComplex n) (alpha : Fin n→Bool)
    (square : Affine (fun x=>f x^2)) : Affine (fun x=>localTwist alpha f x^2) := by
  have h := (S.twist_square_affine alpha).mul square
  convert h using 1
  funext x
  simp only [localTwist_apply,mul_pow,←Finset.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp [zetaEight_sq]

variable {f : Signature AlgebraicComplex n} (D : SystematicSupport f 1)

def twistChart (alpha : Fin n→Bool) : SystematicSupport (localTwist alpha f) 1 where
  ports := D.ports
  injective := D.injective
  encode := D.encode
  affine := D.affine
  free := D.free
  supported z := (twist_support f alpha _).mpr (D.supported z)
  covers x hx := D.covers x ((twist_support f alpha x).mp hx)

theorem twist_affine_iff (square : Affine (fun x=>f x^2)) (alpha : Fin n→Bool) :
    Affine (localTwist alpha f) ↔
      maskSign alpha (R.left D)*f (R.left D)^4=maskSign alpha (R.right D)*f (R.right D)^4 := by
  have h := R.affine_iff_fourth (twistChart D alpha) (twist_square f alpha square)
  simpa only [twistChart,R.left,R.right,twist_fourth] using h

theorem local_iff_two_twists : LocalAffine f ↔
    Affine (localTwist (R.left D) f) ∧ Affine (localTwist (R.right D) f) := by
  constructor
  · intro h
    exact ⟨h _ (R.left_supported D),h _ (R.right_supported D)⟩
  · rintro ⟨hl,hr⟩ alpha supported
    rcases R.supported_words D alpha supported with rfl|rfl
    · exact hl
    · exact hr

theorem local_iff_fourth (square : Affine (fun x=>f x^2)) : LocalAffine f ↔
    (maskSign (R.left D) (R.left D)*f (R.left D)^4=
      maskSign (R.left D) (R.right D)*f (R.right D)^4) ∧
    (maskSign (R.right D) (R.left D)*f (R.left D)^4=
      maskSign (R.right D) (R.right D)*f (R.right D)^4) := by
  rw [local_iff_two_twists,twist_affine_iff D square,twist_affine_iff D square]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalRankOneCriterion
end
