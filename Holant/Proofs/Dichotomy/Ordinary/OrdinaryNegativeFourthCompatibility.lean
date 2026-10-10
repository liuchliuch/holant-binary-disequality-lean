import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineRankOne

/-! Whole-family fourth-power compatibility, before sparse phase extraction.
Either an even-distance two-point restriction fails Affine, two odd-distance
restrictions have a nonAffine product, or one shared identity/octagonal twist
makes every row's supported fourth powers constant. No rank, support shape,
square-Affine hypothesis, or per-row basis choice is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeFourthCompatibility
open Holant Holant.Tractable
namespace R
export OrdinaryNegativeAffineRankOne (uniform uniform_support uniform_fourth sign sign_sq sign_distance)
end R
namespace D
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {s : ℕ} {a : ℕ→ℕ}
variable (F : (i : Fin s)→Signature AlgebraicComplex (a i.val))

def CommonFourth {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  ∀x y,f x≠0→f y≠0→f x^4=f y^4

def EvenFailure : Prop := ∃i x y,F i x≠0 ∧ F i y≠0 ∧ Even (D.distance x y) ∧
  (F i x)^4≠(F i y)^4

def OddFailure : Prop := ∃i j x y u v,F i x≠0 ∧ F i y≠0 ∧ F j u≠0 ∧ F j v≠0 ∧
  Odd (D.distance x y) ∧ Odd (D.distance u v) ∧
    (F i x*F j u)^4≠(F i y*F j v)^4

def Compatible : Prop := (∀i,CommonFourth (F i)) ∨ (∀i,CommonFourth (R.uniform (F i)))

private theorem uniform_equal {n : ℕ} (f : Signature AlgebraicComplex n)
    (x y : Fin n→Bool) (h : f x^4=(-1 : AlgebraicComplex)^D.distance x y*f y^4) :
    R.uniform f x^4=R.uniform f y^4 := by
  rw [R.uniform_fourth,R.uniform_fourth,h,←R.sign_distance]
  calc
    R.sign x*(R.sign x*R.sign y*f y^4)=R.sign x^2*(R.sign y*f y^4) := by ring
    _=R.sign y*f y^4 := by rw [R.sign_sq,one_mul]

/-- The shared twist is determined by an actual odd-distance supported pair.
If there is no such pair, the identity works simultaneously for every row. -/
theorem compatible_of_no_failures (he : ¬EvenFailure F) (ho : ¬OddFailure F) : Compatible F := by
  classical
  have evenEq (i : Fin s) (x y : Fin (a i.val)→Bool) (hx : F i x≠0) (hy : F i y≠0)
      (hd : Even (D.distance x y)) : F i x^4=F i y^4 := by
    by_contra h
    exact he ⟨i,x,y,hx,hy,hd,h⟩
  have pairEq (i j : Fin s) (x y : Fin (a i.val)→Bool) (u v : Fin (a j.val)→Bool)
      (hx : F i x≠0) (hy : F i y≠0) (hu : F j u≠0) (hv : F j v≠0)
      (hd : Odd (D.distance x y)) (he : Odd (D.distance u v)) :
      (F i x*F j u)^4=(F i y*F j v)^4 := by
    by_contra h
    exact ho ⟨i,j,x,y,u,v,hx,hy,hu,hv,hd,he,h⟩
  by_cases oddPair : ∃i x y,F i x≠0 ∧ F i y≠0 ∧ Odd (D.distance x y)
  · obtain ⟨i,x,y,hx,hy,hxy⟩ := oddPair
    have square : (F i x^4)^2=(F i y^4)^2 := by
      have h := pairEq i i x y x y hx hy hx hy hxy hxy
      calc
        (F i x^4)^2=(F i x*F i x)^4 := by ring
        _=(F i y*F i y)^4 := h
        _=(F i y^4)^2 := by ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp square with equal|negative
    · left
      intro j u v hu hv
      rcases Nat.even_or_odd (D.distance u v) with ev|od
      · exact evenEq j u v hu hv ev
      · have h := pairEq i j x y u v hx hy hu hv hxy od
        simp only [mul_pow,equal] at h
        exact mul_left_cancel₀ (pow_ne_zero 4 hy) h
    · right
      intro j u v hu hv
      have hu' := (R.uniform_support (F j) u).mp hu
      have hv' := (R.uniform_support (F j) v).mp hv
      apply uniform_equal
      rcases Nat.even_or_odd (D.distance u v) with ev|od
      · rw [ev.neg_one_pow,one_mul]
        exact evenEq j u v hu' hv' ev
      · have h := pairEq i j x y u v hx hy hu' hv' hxy od
        simp only [mul_pow,negative] at h
        have hz : F i y^4*(F j u^4+F j v^4)=0 := by linear_combination -h
        have hz' := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 4 hy)
        rw [od.neg_one_pow]
        linear_combination hz'
  · left
    intro i x y hx hy
    rcases Nat.even_or_odd (D.distance x y) with ev|od
    · exact evenEq i x y hx hy ev
    · exact False.elim (oddPair ⟨i,x,y,hx,hy,od⟩)

/-- The two failure constructors have concrete one- or two-row physical
suppliers; the compatible constructor always uses ONE global phase choice. -/
theorem alternative : EvenFailure F ∨ OddFailure F ∨ Compatible F := by
  classical
  by_cases he : EvenFailure F
  · exact Or.inl he
  by_cases ho : OddFailure F
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr (compatible_of_no_failures F he ho))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeFourthCompatibility
end
