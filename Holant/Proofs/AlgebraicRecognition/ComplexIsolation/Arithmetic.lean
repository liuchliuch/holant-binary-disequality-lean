import Holant.Proofs.AlgebraicRecognition.RealIsolation
import Holant.Algebraic.GaussianEmbedding
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.GCongr


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
open Holant.Algebraic
open RealIsolation (derivativeCode derivativeCode_correct)

def gaussian (q : ℚ × ℚ) : GaussianRational := ⟨q.1, q.2⟩
def size (z : GaussianRational) : ℚ := |z.re| + |z.im|
noncomputable def value (q : ℚ × ℚ) : ℂ := gaussianToComplex (gaussian q)
noncomputable def taxicab (z : ℂ) : ℝ := |z.re| + |z.im|

theorem taxicab_nonneg (z : ℂ) : 0 ≤ taxicab z := add_nonneg (abs_nonneg _) (abs_nonneg _)
theorem norm_le_taxicab (z : ℂ) : ‖z‖ ≤ taxicab z := Complex.norm_le_abs_re_add_abs_im z
theorem taxicab_le_norm (z : ℂ) : taxicab z ≤ 2 * ‖z‖ := by
  unfold taxicab
  linarith [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]

theorem taxicab_continuous : Continuous taxicab :=
  Complex.continuous_re.abs.add Complex.continuous_im.abs

@[simp] theorem size_cast (z : GaussianRational) :
    (size z : ℝ) = taxicab (gaussianToComplex z) := by
  simp [size, taxicab, gaussianToComplex_apply]

theorem norm_gaussian_le (z : GaussianRational) : ‖gaussianToComplex z‖ ≤ (size z : ℝ) := by
  rw [size_cast]
  exact norm_le_taxicab _

theorem size_nonneg (z : GaussianRational) : 0 ≤ size z := add_nonneg (abs_nonneg _) (abs_nonneg _)

def evalGaussian (z : GaussianRational) : RationalPolynomialCode → GaussianRational
  | [] => 0
  | (k, q) :: rest => (q : GaussianRational) * z ^ k + evalGaussian z rest

theorem evalGaussian_correct (z : GaussianRational) (p : RationalPolynomialCode) :
    gaussianToComplex (evalGaussian z p) = Polynomial.aeval (gaussianToComplex z) p.polynomial := by
  induction p with
  | nil => simp [evalGaussian, RationalPolynomialCode.polynomial]
  | cons t ts ih =>
    rcases t with ⟨k, q⟩
    rw [evalGaussian, map_add, map_mul, map_pow, ih, map_ratCast]
    change (q : ℂ) * gaussianToComplex z ^ k + Polynomial.aeval (gaussianToComplex z) (RationalPolynomialCode.polynomial ts) =
      Polynomial.aeval (gaussianToComplex z) (Polynomial.monomial k q + (RationalPolynomialCode.polynomial ts))
    rw [map_add, Polynomial.aeval_monomial]
    simp

/-- A rational bound on a polynomial throughout the disk of radius B at zero. -/
def majorant (B : ℚ) : RationalPolynomialCode → ℚ
  | [] => 0
  | (k, q) :: rest => |q| * B ^ k + majorant B rest

theorem majorant_nonneg {B : ℚ} (hB : 0 ≤ B) (p : RationalPolynomialCode) :
    0 ≤ majorant B p := by
  induction p with
  | nil => exact le_rfl
  | cons t ts ih => exact add_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hB _)) ih

theorem norm_eval_le_majorant {B : ℚ} (hB : 0 ≤ B) {z : ℂ} (hz : ‖z‖ ≤ (B : ℝ))
    (p : RationalPolynomialCode) : ‖Polynomial.aeval z p.polynomial‖ ≤ (majorant B p : ℝ) := by
  induction p with
  | nil => simp [RationalPolynomialCode.polynomial, majorant]
  | cons t ts ih =>
    rcases t with ⟨k, q⟩
    simp only [RationalPolynomialCode.polynomial, map_add, Polynomial.aeval_monomial,
      majorant, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_abs]
    calc
      _ ≤ ‖(q : ℂ) * z ^ k‖ + ‖Polynomial.aeval z (RationalPolynomialCode.polynomial ts)‖ := norm_add_le _ _
      _ ≤ |(q : ℝ)| * (B : ℝ) ^ k + (majorant B ts : ℝ) := by
        apply add_le_add _ ih
        simp only [norm_mul, norm_pow, Complex.norm_ratCast]
        gcongr

def curvature (p : RationalPolynomialCode) (B : ℚ) : ℚ :=
  majorant B (derivativeCode (derivativeCode p))

theorem curvature_nonneg (p : RationalPolynomialCode) {B : ℚ} (hB : 0 ≤ B) :
    0 ≤ curvature p B := majorant_nonneg hB _

/-- The derivative Lipschitz constant is computed from actual second-derivative
coefficients, not provided as a certificate correctness field. -/
theorem derivative_difference_bound (p : RationalPolynomialCode) {B : ℚ} (hB : 0 ≤ B)
    {x y : ℂ} (hx : ‖x‖ ≤ (B : ℝ)) (hy : ‖y‖ ≤ (B : ℝ)) :
    ‖Polynomial.aeval y p.polynomial.derivative - Polynomial.aeval x p.polynomial.derivative‖ ≤
      (curvature p B : ℝ) * ‖y - x‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => p.polynomial.derivative.differentiableAt_aeval)
    (fun z hz => ?_) (convex_closedBall (0 : ℂ) (B : ℝ))
    (by simpa using hx) (by simpa using hy)
  rw [Polynomial.deriv_aeval]
  have hz' : ‖z‖ ≤ (B : ℝ) := by simpa using hz
  simpa only [curvature, derivativeCode_correct] using norm_eval_le_majorant hB hz'
    (derivativeCode (derivativeCode p))

/-- Density is proved with rational coordinate approximation, independently of
any root-existence theorem or choice-based runtime codec. -/
theorem exists_rational_near (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ × ℚ, ‖value q - z‖ < ε := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show z.re - ε / 4 < z.re + ε / 4 by linarith)
  obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show z.im - ε / 4 < z.im + ε / 4 by linarith)
  refine ⟨(a, b), ?_⟩
  have ha : |(a : ℝ) - z.re| < ε / 4 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hb : |(b : ℝ) - z.im| < ε / 4 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hn := Complex.norm_le_abs_re_add_abs_im (value (a, b) - z)
  simp [value, gaussian, gaussianToComplex_apply] at hn ⊢
  linarith

theorem exists_rational_mem_open {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    ∃ q : ℚ × ℚ, value q ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨q, hq⟩ := exists_rational_near z hε
  exact ⟨q, hball (by simpa only [Metric.mem_ball, dist_eq_norm] using hq)⟩

end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
