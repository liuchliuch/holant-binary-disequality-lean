import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.Soundness
import Mathlib.FieldTheory.Perfect


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation

/-- Approximate the inverse derivative by rational real and imaginary parts.
The strict margin is obtained from continuity at the genuine inverse. -/
theorem exists_inverseSlope {d : ℂ} (hd : d ≠ 0) :
    ∃ b : ℚ × ℚ, taxicab (1 - value b * d) < (1 : ℝ) / 8 := by
  have hU : IsOpen {b : ℂ | taxicab (1 - b * d) < (1 : ℝ) / 8} :=
    isOpen_lt (taxicab_continuous.comp (continuous_const.sub
      (continuous_id.mul continuous_const))) continuous_const
  have hz : d⁻¹ ∈ {b : ℂ | taxicab (1 - b * d) < (1 : ℝ) / 8} := by
    change taxicab (1-d⁻¹*d) < (1 : ℝ)/8
    rw [inv_mul_cancel₀ hd, sub_self]
    norm_num [taxicab]
  exact exists_rational_mem_open hU hz

/-- Completeness does not require the root to be real, or restrict the degree
of the rational input polynomial. The entire returned rectangle fits in the
requested neighborhood, which is stronger than a shrinking radius alone. -/
theorem exists_certificate (p : RationalPolynomialCode) (z : ℂ)
    (hp : Polynomial.aeval z p.polynomial = 0)
    (hd : Polynomial.aeval z p.polynomial.derivative ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Certificate, t.check p = true ∧ (t.rootCode p).Represents z ∧
      ∀ w : ℂ, t.rectangle.Contains w → ‖w - z‖ < ε := by
  obtain ⟨b, hb⟩ := exists_inverseSlope hd
  obtain ⟨B, hB, _⟩ := exists_rat_btwn
    (show taxicab z + 1 < taxicab z + 2 by linarith)
  let A : ℝ := taxicab (value b) * (curvature p B : ℝ)
  -- The coefficient bound is now fixed. An open neighborhood at radius zero
  -- supplies a positive rational radius satisfying every required margin.
  let V : Set ℝ := {r | r < 1 / 4 ∧ r < ε / 4 ∧ A * (2 * r) < 1 / 8}
  have hV : IsOpen V :=
    (isOpen_lt continuous_id continuous_const).inter
      ((isOpen_lt continuous_id continuous_const).inter
        (isOpen_lt (continuous_const.mul (continuous_const.mul continuous_id)) continuous_const))
  have hV0 : (0 : ℝ) ∈ V := by
    change 0 < (1 : ℝ) / 4 ∧ 0 < ε / 4 ∧ A * (2 * 0) < 1 / 8
    exact ⟨by norm_num, by linarith, by norm_num⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV 0 hV0
  obtain ⟨r, hr0, hrδ⟩ := exists_rat_btwn hδ
  have hrV : (r : ℝ) ∈ V := hδV (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr0] using hrδ)
  rcases hrV with ⟨hr₁, hrε, hrA⟩
  -- Keep all strict checker inequalities while moving the center to Q(i).
  let U : Set ℂ := {c |
    taxicab c + 2 * (r : ℝ) < (B : ℝ) ∧
    taxicab (1 - value b * Polynomial.aeval c p.polynomial.derivative) +
      A * (2 * (r : ℝ)) < 1 / 2 ∧
    taxicab (value b * Polynomial.aeval c p.polynomial) < (r : ℝ) / 4 ∧
    ‖c - z‖ < (r : ℝ) / 4}
  have hU : IsOpen U :=
    (isOpen_lt (taxicab_continuous.add continuous_const) continuous_const).inter
      ((isOpen_lt ((taxicab_continuous.comp (continuous_const.sub
        (continuous_const.mul p.polynomial.derivative.continuous_aeval))).add continuous_const)
          continuous_const).inter
      ((isOpen_lt (taxicab_continuous.comp
        (continuous_const.mul p.polynomial.continuous_aeval)) continuous_const).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)))
  have hzU : z ∈ U := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith
    · change taxicab (1 - value b * Polynomial.aeval z p.polynomial.derivative) +
        A * (2 * (r : ℝ)) < 1 / 2
      linarith
    · simp only [hp, mul_zero, taxicab, Complex.zero_re, Complex.zero_im, abs_zero, add_zero]
      linarith
    · simp only [sub_self, norm_zero]
      linarith
  obtain ⟨q, hqB, hqL, hqR, hqz⟩ := exists_rational_mem_open hU hzU
  let t : Certificate := ⟨q, b, r, B⟩
  have ht : t.check p = true := (Certificate.check_iff p t).mpr
    ⟨hr0, hqB, hqL, hqR⟩
  have hzq : ‖z - value q‖ < (r : ℝ) := by
    rw [norm_sub_rev]
    linarith
  have hzbox : t.rectangle.Contains z := t.contains_of_norm_lt hzq
  refine ⟨t, ht, Certificate.represents_of_check_of_root ht hzbox hp, ?_⟩
  intro w hw
  have hwq := t.norm_lt_of_contains hw
  have htri : ‖w - z‖ ≤ ‖w - value q‖ + ‖value q - z‖ := by
    simpa using norm_add_le (w - value q) (value q - z)
  change ‖w - value q‖ < 2 * (r : ℝ) at hwq
  linarith

/-- Characteristic-zero separability discharges simplicity for every algebraic
complex number, using its actual minimal polynomial over Q. -/
theorem exists_algebraic_certificate (z : ℂ) (hz : IsAlgebraic ℚ z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (p : RationalPolynomialCode) (t : Certificate),
      p.polynomial = minpoly ℚ z ∧ t.check p = true ∧ (t.rootCode p).Represents z ∧
      ∀ w : ℂ, t.rectangle.Contains w → ‖w - z‖ < ε := by
  have hmin : Polynomial.aeval z (minpoly ℚ z) = 0 := minpoly.aeval ℚ z
  have hsep : (minpoly ℚ z).Separable := (minpoly.irreducible hz.isIntegral).separable
  have hd := hsep.aeval_derivative_ne_zero hmin
  obtain ⟨p, hp⟩ := RationalPolynomialCode.exists_code (minpoly ℚ z)
  obtain ⟨t, ht, hrep, hsmall⟩ := exists_certificate p z
    (by simpa only [hp] using hmin) (by simpa only [hp] using hd) hε
  exact ⟨p, t, hp, ht, hrep, hsmall⟩

end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
