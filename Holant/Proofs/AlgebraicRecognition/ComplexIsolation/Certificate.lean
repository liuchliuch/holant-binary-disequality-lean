import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.Arithmetic


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
open Holant.Algebraic
open RealIsolation (derivativeCode derivativeCode_correct)

structure Certificate where
  center : ℚ × ℚ
  inverseSlope : ℚ × ℚ
  radius : ℚ
  magnitude : ℚ
  deriving DecidableEq, Encodable

def Conditions (p : RationalPolynomialCode) (B : ℚ) (c b : ℂ) (r : ℝ) : Prop :=
  0 < r ∧ taxicab c + 2 * r < (B : ℝ) ∧
    taxicab (1 - b * Polynomial.aeval c p.polynomial.derivative) +
      taxicab b * (curvature p B : ℝ) * (2 * r) < 1 / 2 ∧
    taxicab (b * Polynomial.aeval c p.polynomial) < r / 4

namespace Certificate

def slopeError (p : RationalPolynomialCode) (t : Certificate) : ℚ :=
  size (1 - gaussian t.inverseSlope * evalGaussian (gaussian t.center) (derivativeCode p))

def residual (p : RationalPolynomialCode) (t : Certificate) : ℚ :=
  size (gaussian t.inverseSlope * evalGaussian (gaussian t.center) p)

def check (p : RationalPolynomialCode) (t : Certificate) : Bool :=
  decide (0 < t.radius ∧ size (gaussian t.center) + 2 * t.radius < t.magnitude ∧
    t.slopeError p + size (gaussian t.inverseSlope) * curvature p t.magnitude *
      (2 * t.radius) < 1 / 2 ∧ t.residual p < t.radius / 4)

def rectangle (t : Certificate) : RationalRectangle :=
  ⟨t.center.1 - t.radius, t.center.1 + t.radius,
    t.center.2 - t.radius, t.center.2 + t.radius⟩

def rootCode (p : RationalPolynomialCode) (t : Certificate) : RootCode :=
  ⟨p, t.rectangle⟩

@[simp] theorem value_re (q : ℚ × ℚ) : (value q).re = (q.1 : ℝ) := by
  simp [value, gaussian, gaussianToComplex_apply]

@[simp] theorem value_im (q : ℚ × ℚ) : (value q).im = (q.2 : ℝ) := by
  simp [value, gaussian, gaussianToComplex_apply]

@[simp] theorem slopeError_cast (p : RationalPolynomialCode) (t : Certificate) :
    (t.slopeError p : ℝ) =
      taxicab (1 - value t.inverseSlope * Polynomial.aeval (value t.center) p.polynomial.derivative) := by
  rw [slopeError, size_cast, map_sub, map_one, map_mul, evalGaussian_correct,
    derivativeCode_correct]
  rfl

@[simp] theorem residual_cast (p : RationalPolynomialCode) (t : Certificate) :
    (t.residual p : ℝ) =
      taxicab (value t.inverseSlope * Polynomial.aeval (value t.center) p.polynomial) := by
  rw [residual, size_cast, map_mul, evalGaussian_correct]
  rfl

theorem check_iff (p : RationalPolynomialCode) (t : Certificate) :
    t.check p = true ↔
      Conditions p t.magnitude (value t.center) (value t.inverseSlope) t.radius := by
  simp only [check, decide_eq_true_eq, Conditions]
  have h₁ : (0 : ℚ) < t.radius ↔ (0 : ℝ) < (t.radius : ℝ) := by norm_cast
  have h₂ : size (gaussian t.center) + 2 * t.radius < t.magnitude ↔
      taxicab (value t.center) + 2 * (t.radius : ℝ) < (t.magnitude : ℝ) := by
    change _ ↔ taxicab (gaussianToComplex (gaussian t.center)) + 2 * (t.radius : ℝ) < (t.magnitude : ℝ)
    rw [← size_cast]
    norm_cast
  have h₃ : t.slopeError p + size (gaussian t.inverseSlope) * curvature p t.magnitude *
      (2 * t.radius) < (1 : ℚ) / 2 ↔
      taxicab (1 - value t.inverseSlope * Polynomial.aeval (value t.center) p.polynomial.derivative) +
        taxicab (value t.inverseSlope) * (curvature p t.magnitude : ℝ) *
          (2 * (t.radius : ℝ)) < (1 : ℝ) / 2 := by
    rw [← slopeError_cast]
    unfold value
    rw [← size_cast]
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ) (p := t.slopeError p + size (gaussian t.inverseSlope) *
        curvature p t.magnitude * (2 * t.radius)) (q := (1 : ℚ) / 2)).symm
  have h₄ : t.residual p < t.radius / 4 ↔
      taxicab (value t.inverseSlope * Polynomial.aeval (value t.center) p.polynomial) <
        (t.radius : ℝ) / 4 := by
    rw [← residual_cast]
    norm_cast
  exact and_congr h₁ (and_congr h₂ (and_congr h₃ h₄))

theorem contains_of_norm_lt (t : Certificate) {z : ℂ}
    (hz : ‖z - value t.center‖ < (t.radius : ℝ)) : t.rectangle.Contains z := by
  have hr := (Complex.abs_re_le_norm (z - value t.center)).trans_lt hz
  have hi := (Complex.abs_im_le_norm (z - value t.center)).trans_lt hz
  simp only [Complex.sub_re, Complex.sub_im, value_re, value_im] at hr hi
  rcases abs_lt.mp hr with ⟨hr₁, hr₂⟩
  rcases abs_lt.mp hi with ⟨hi₁, hi₂⟩
  simp only [RationalRectangle.Contains, rectangle, Rat.cast_sub, Rat.cast_add]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The *whole* output rectangle is in the outer uniqueness disk. -/
theorem norm_lt_of_contains (t : Certificate) {z : ℂ} (hz : t.rectangle.Contains z) :
    ‖z - value t.center‖ < 2 * (t.radius : ℝ) := by
  rcases hz with ⟨hr₁, hr₂, hi₁, hi₂⟩
  simp only [rectangle, Rat.cast_sub, Rat.cast_add] at hr₁ hr₂ hi₁ hi₂
  have hr : |z.re - (t.center.1 : ℝ)| < (t.radius : ℝ) :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  have hi : |z.im - (t.center.2 : ℝ)| < (t.radius : ℝ) :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  have hn := norm_le_taxicab (z - value t.center)
  simp only [taxicab, Complex.sub_re, Complex.sub_im, value_re, value_im] at hn
  linarith

end Certificate
end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
