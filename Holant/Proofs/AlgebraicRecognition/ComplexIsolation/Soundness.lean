import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.Certificate


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation

noncomputable def newton (p : RationalPolynomialCode) (b z : ℂ) : ℂ :=
  z - b * Polynomial.aeval z p.polynomial

namespace Conditions
open scoped NNReal
variable {p : RationalPolynomialCode} {B : ℚ} {c b : ℂ} {r : ℝ}

theorem magnitude_nonneg (h : Conditions p B c b r) : 0 ≤ B := by
  have : (0 : ℝ) < (B : ℝ) := by linarith [taxicab_nonneg c, h.1, h.2.1]
  exact_mod_cast this.le

theorem error_lt (h : Conditions p B c b r) :
    taxicab (1 - b * Polynomial.aeval c p.polynomial.derivative) < 1 / 2 := by
  have hH : (0 : ℝ) ≤ (curvature p B : ℝ) := by
    exact_mod_cast curvature_nonneg p h.magnitude_nonneg
  have ht := mul_nonneg (mul_nonneg (taxicab_nonneg b) hH) (by linarith [h.1] : 0 ≤ 2 * r)
  linarith [h.2.2.1]

theorem slope_ne_zero (h : Conditions p B c b r) : b ≠ 0 := by
  intro hb
  have he := h.error_lt
  norm_num [hb, taxicab] at he

theorem polynomial_ne_zero (h : Conditions p B c b r) : p.polynomial ≠ 0 := by
  intro hp
  have he := h.error_lt
  norm_num [hp, taxicab] at he

theorem norm_le_magnitude (h : Conditions p B c b r) {z : ℂ}
    (hz : ‖z - c‖ ≤ 2 * r) : ‖z‖ ≤ (B : ℝ) := by
  have hn : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
    simpa using norm_add_le (z - c) c
  linarith [norm_le_taxicab c, h.2.1]

theorem newton_derivative_bound (h : Conditions p B c b r) {z : ℂ}
    (hz : ‖z - c‖ ≤ 2 * r) :
    ‖1 - b * Polynomial.aeval z p.polynomial.derivative‖ ≤ (1 : ℝ) / 2 := by
  have hc : ‖c - c‖ ≤ 2 * r := by simp; linarith [h.1]
  have hd := derivative_difference_bound p h.magnitude_nonneg
    (h.norm_le_magnitude hc) (h.norm_le_magnitude hz)
  have hH : (0 : ℝ) ≤ (curvature p B : ℝ) := by
    exact_mod_cast curvature_nonneg p h.magnitude_nonneg
  calc
    _ = ‖(1 - b * Polynomial.aeval c p.polynomial.derivative) -
        b * (Polynomial.aeval z p.polynomial.derivative -
          Polynomial.aeval c p.polynomial.derivative)‖ := by congr 1; ring
    _ ≤ ‖1 - b * Polynomial.aeval c p.polynomial.derivative‖ +
        ‖b * (Polynomial.aeval z p.polynomial.derivative -
          Polynomial.aeval c p.polynomial.derivative)‖ := norm_sub_le _ _
    _ ≤ taxicab (1 - b * Polynomial.aeval c p.polynomial.derivative) +
        taxicab b * ((curvature p B : ℝ) * ‖z - c‖) := by
      apply add_le_add (norm_le_taxicab _)
      rw [norm_mul]
      exact mul_le_mul (norm_le_taxicab b) hd (norm_nonneg _) (taxicab_nonneg b)
    _ ≤ taxicab (1 - b * Polynomial.aeval c p.polynomial.derivative) +
        taxicab b * (curvature p B : ℝ) * (2 * r) := by
      rw [mul_assoc]
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hz hH) (taxicab_nonneg b))
    _ ≤ 1 / 2 := h.2.2.1.le

theorem newton_hasDerivAt (z : ℂ) :
    HasDerivAt (newton p b) (1 - b * Polynomial.aeval z p.polynomial.derivative) z := by
  exact (hasDerivAt_id z).sub ((p.polynomial.hasDerivAt_aeval z).const_mul b)

/-- A bound valid on the outer disk, including its boundary. -/
theorem newton_lipschitz (h : Conditions p B c b r) {x y : ℂ}
    (hx : ‖x - c‖ ≤ 2 * r) (hy : ‖y - c‖ ≤ 2 * r) :
    ‖newton p b y - newton p b x‖ ≤ (1 / 2 : ℝ) * ‖y - x‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (newton_hasDerivAt (p := p) (b := b) z).differentiableAt)
    (fun z hz => ?_) (convex_closedBall c (2 * r))
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy)
  rw [(newton_hasDerivAt (p := p) (b := b) z).deriv]
  exact h.newton_derivative_bound (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)

theorem newton_maps_inner (h : Conditions p B c b r) :
    Set.MapsTo (newton p b) (Metric.closedBall c (r / 2)) (Metric.closedBall c (r / 2)) := by
  intro z hz
  have hz' : ‖z - c‖ ≤ r / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hc : ‖c - c‖ ≤ 2 * r := by simp; linarith [h.1]
  have hzc : ‖z - c‖ ≤ 2 * r := by linarith [h.1]
  have hl := h.newton_lipschitz hc hzc
  have he : ‖newton p b c - c‖ < r / 4 := by
    calc
      _ = ‖b * Polynomial.aeval c p.polynomial‖ := by
        unfold newton
        rw [sub_sub_cancel_left, norm_neg]
      _ ≤ taxicab (b * Polynomial.aeval c p.polynomial) := norm_le_taxicab _
      _ < r / 4 := h.2.2.2
  have ht : ‖newton p b z - c‖ ≤
      ‖newton p b z - newton p b c‖ + ‖newton p b c - c‖ := by
    simpa using norm_add_le (newton p b z - newton p b c) (newton p b c - c)
  simp only [Metric.mem_closedBall, dist_eq_norm]
  linarith

/-- Banach's theorem is used only in a proof of existence, never as an
uncomputable runtime root selector. -/
theorem exists_root (h : Conditions p B c b r) :
    ∃ z : ℂ, ‖z - c‖ ≤ r / 2 ∧ Polynomial.aeval z p.polynomial = 0 := by
  let s := Metric.closedBall c (r / 2)
  have hmap : Set.MapsTo (newton p b) s s := h.newton_maps_inner
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) (hmap.restrict (newton p b) s s) := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      have hx : ‖(x : ℂ) - c‖ ≤ r / 2 := by
        simpa only [s, Metric.mem_closedBall, dist_eq_norm] using x.property
      have hy : ‖(y : ℂ) - c‖ ≤ r / 2 := by
        simpa only [s, Metric.mem_closedBall, dist_eq_norm] using y.property
      have hl := h.newton_lipschitz (by linarith [h.1] : ‖(y : ℂ) - c‖ ≤ 2 * r)
        (by linarith [h.1] : ‖(x : ℂ) - c‖ ≤ 2 * r)
      change dist (newton p b x) (newton p b y) ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist (x : ℂ) y
      simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hl
  have hc : c ∈ s := by
    simp only [s, Metric.mem_closedBall, dist_self]
    linarith [h.1]
  obtain ⟨z, hz, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    (Metric.isClosed_closedBall.isComplete) hmap hcontract hc (edist_ne_top _ _)
  refine ⟨z, by simpa only [s, Metric.mem_closedBall, dist_eq_norm] using hz, ?_⟩
  have heq : z - b * Polynomial.aeval z p.polynomial = z := hfix
  have hz0 : b * Polynomial.aeval z p.polynomial = 0 := by
    exact sub_eq_self.mp heq
  exact (mul_eq_zero.mp hz0).resolve_left h.slope_ne_zero

theorem roots_unique (h : Conditions p B c b r) {x y : ℂ}
    (hx : ‖x - c‖ ≤ 2 * r) (hy : ‖y - c‖ ≤ 2 * r)
    (hpx : Polynomial.aeval x p.polynomial = 0)
    (hpy : Polynomial.aeval y p.polynomial = 0) : y = x := by
  have hl := h.newton_lipschitz hx hy
  simp only [newton, hpx, hpy, mul_zero, sub_zero] at hl
  have : ‖y - x‖ = 0 := by linarith [norm_nonneg (y - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end Conditions

namespace Certificate

theorem check_sound {p : RationalPolynomialCode} {t : Certificate} (ht : t.check p = true) :
    ∃ z : ℂ, (t.rootCode p).Represents z := by
  have h := (check_iff p t).mp ht
  obtain ⟨z, hz, hpz⟩ := h.exists_root
  have hzr : ‖z - value t.center‖ < (t.radius : ℝ) := by linarith [h.1]
  refine ⟨z, h.polynomial_ne_zero, t.contains_of_norm_lt hzr, hpz, ?_⟩
  intro w hw hpw
  exact h.roots_unique (by linarith [h.1]) (t.norm_lt_of_contains hw).le hpz hpw

theorem represents_of_check_of_root {p : RationalPolynomialCode} {t : Certificate}
    (ht : t.check p = true) {z : ℂ} (hz : t.rectangle.Contains z)
    (hpz : Polynomial.aeval z p.polynomial = 0) : (t.rootCode p).Represents z := by
  have h := (check_iff p t).mp ht
  exact ⟨h.polynomial_ne_zero, hz, hpz,
    fun w hw hpw => h.roots_unique (t.norm_lt_of_contains hz).le
      (t.norm_lt_of_contains hw).le hpz hpw⟩

theorem check_rejects_constant {p : RationalPolynomialCode} (t : Certificate) (q : ℚ)
    (hp : p.polynomial = Polynomial.C q) : t.check p = false := by
  cases hcheck : t.check p with
  | false => rfl
  | true =>
    have he := ((check_iff p t).mp hcheck).error_lt
    norm_num [hp, taxicab] at he

theorem check_rejects_zero {p : RationalPolynomialCode} (t : Certificate)
    (hp : p.polynomial = 0) : t.check p = false := by
  apply t.check_rejects_constant 0
  simpa using hp

theorem check_rejects_nonpositive_radius (p : RationalPolynomialCode) (t : Certificate)
    (hr : t.radius ≤ 0) : t.check p = false := by
  simp only [check, decide_eq_false_iff_not]
  exact fun h => (not_lt_of_ge hr) h.1

end Certificate
end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
