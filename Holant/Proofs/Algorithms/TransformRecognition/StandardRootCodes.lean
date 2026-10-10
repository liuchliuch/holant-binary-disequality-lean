import Holant.Proofs.Algorithms.TransformRecognition.RationalRootCode


namespace Holant.LocalDrafts.MainChain.TransformRecognition.StandardRootCodes
open Holant.LocalDrafts.EffectiveAlgebraic Polynomial Holant.Tractable

def imaginary : RootCode := ⟨[(2,1),(0,1)],⟨-1,1,0,2⟩⟩
def positiveSqrtTwo : RootCode := ⟨[(2,1),(0,-2)],⟨1,2,-1,1⟩⟩

theorem imaginary_polynomial : imaginary.polynomial = X^2+1 := by
  simp [imaginary,RootCode.polynomial,RationalPolynomialCode.polynomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]

theorem sqrt_polynomial : positiveSqrtTwo.polynomial = X^2-C 2 := by
  simp [positiveSqrtTwo,RootCode.polynomial,RationalPolynomialCode.polynomial,
    ← Polynomial.C_mul_X_pow_eq_monomial,sub_eq_add_neg]

theorem imaginary_represents : imaginary.Represents Complex.I := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    have he := congrArg (fun p : ℚ[X] => p.coeff 2) h
    norm_num [imaginary_polynomial,Polynomial.coeff_one] at he
  · norm_num [imaginary,RationalRectangle.Contains]
  · simp [imaginary_polynomial]
  · intro z hz hp
    have hs : z^2 = Complex.I^2 := by
      have he : z^2+1=0 := by simpa [imaginary_polynomial] using hp
      rw [Complex.I_sq]
      linear_combination he
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · exact h
    · subst z
      norm_num [imaginary,RationalRectangle.Contains] at hz

theorem sqrtTwo_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
  have hn := Real.sqrt_nonneg (2:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  constructor <;> nlinarith

theorem sqrt_represents : positiveSqrtTwo.Represents (Real.sqrt 2 : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ)^2=2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    have he := congrArg (fun p : ℚ[X] => p.coeff 2) h
    norm_num [sqrt_polynomial] at he
  · simpa [positiveSqrtTwo,RationalRectangle.Contains] using sqrtTwo_bounds
  · simp [sqrt_polynomial,hs]
  · intro z hz hp
    have hzsq : z^2=(Real.sqrt 2 : ℂ)^2 := by
      rw [hs]
      have he : z^2-2=0 := by simpa [sqrt_polynomial] using hp
      exact sub_eq_zero.mp he
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hzsq with h | h
    · exact h
    · subst z
      have hn := Real.sqrt_nonneg (2:ℝ)
      have hl := hz.1
      simp only [positiveSqrtTwo,RationalRectangle.Contains,
        Complex.neg_re,Complex.ofReal_re] at hl
      norm_num at hl
      linarith

/-- Two literal descriptors and their specified values. No runtime choice. -/
def descriptors : Fin 2 → RootCode := ![imaginary,positiveSqrtTwo]
noncomputable def values : Fin 2 → ℂ := ![Complex.I,(Real.sqrt 2 : ℂ)]

theorem represents : ∀ i, (descriptors i).Represents (values i) := by
  intro i
  fin_cases i
  · exact imaginary_represents
  · exact sqrt_represents

theorem eighthRoot_of_bindings (i t u : ℂ)
    (hi : imaginary.Represents i) (ht : positiveSqrtTwo.Represents t)
    (hu : u*t=1+i) : u=(zetaEight : ℂ) := by
  have hie : i=Complex.I := imaginary_represents.2.2.2 i hi.2.1 hi.2.2.1
  have hte : t=(Real.sqrt 2 : ℂ) := sqrt_represents.2.2.2 t ht.2.1 ht.2.2.1
  rw [hie,hte] at hu
  rw [coe_zetaEight]
  apply (eq_div_iff ?_).mpr hu
  exact_mod_cast (ne_of_gt (lt_trans (by norm_num : (0:ℝ)<1) sqrtTwo_bounds.1))

end Holant.LocalDrafts.MainChain.TransformRecognition.StandardRootCodes
