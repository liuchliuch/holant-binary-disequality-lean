import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
Semantic algebraic complex numbers for the manuscript's standard signature classes.
This is the actual subfield of `ℂ` algebraic over `ℚ`, not a formal indeterminate
or an effective encoding. No computability or bit-complexity claim follows from
using this carrier. The positive real square root fixes the source's phase choice.
-/

namespace Holant.Tractable

noncomputable section

abbrev AlgebraicComplex := algebraicClosure ℚ ℂ

/-- The complex imaginary unit, with its algebraicity certificate. -/
def imaginaryUnit : AlgebraicComplex := ⟨Complex.I, Complex.isIntegral_I ℚ⟩

@[simp] theorem coe_imaginaryUnit : (imaginaryUnit : ℂ) = Complex.I := rfl

@[simp] theorem imaginaryUnit_sq : imaginaryUnit ^ 2 = -1 := by
  apply Subtype.ext
  exact Complex.I_sq

@[simp] theorem imaginaryUnit_pow_four : imaginaryUnit ^ 4 = 1 := by
  calc
    imaginaryUnit ^ 4 = (imaginaryUnit ^ 2) ^ 2 := by ring
    _ = 1 := by rw [imaginaryUnit_sq]; ring

private theorem sqrtTwo_integral : IsIntegral ℚ (Real.sqrt 2 : ℂ) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  have h : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  rw [h]
  exact isIntegral_natCast 2

/-- Positive `√2`, embedded in the actual algebraic-complex field. -/
def sqrtTwo : AlgebraicComplex := ⟨(Real.sqrt 2 : ℂ), sqrtTwo_integral⟩

@[simp] theorem coe_sqrtTwo : (sqrtTwo : ℂ) = (Real.sqrt 2 : ℂ) := rfl

@[simp] theorem sqrtTwo_sq : sqrtTwo ^ 2 = 2 := by
  apply Subtype.ext
  change (Real.sqrt 2 : ℂ) ^ 2 = 2
  norm_cast
  exact Real.sq_sqrt (by norm_num)

theorem sqrtTwo_ne_zero : sqrtTwo ≠ 0 := by
  intro h
  have := sqrtTwo_sq
  rw [h] at this
  norm_num at this

/-- The manuscript's exact eighth-root choice `(1+i)/√2`. -/
def zetaEight : AlgebraicComplex := (1 + imaginaryUnit) / sqrtTwo

@[simp] theorem coe_zetaEight : (zetaEight : ℂ) =
    (1 + Complex.I) / (Real.sqrt 2 : ℂ) := rfl

@[simp] theorem zetaEight_sq : zetaEight ^ 2 = imaginaryUnit := by
  rw [zetaEight, div_pow, sqrtTwo_sq]
  have h := imaginaryUnit_sq
  linear_combination h / 2

@[simp] theorem zetaEight_pow_four : zetaEight ^ 4 = -1 := by
  calc
    zetaEight ^ 4 = (zetaEight ^ 2) ^ 2 := by ring
    _ = -1 := by rw [zetaEight_sq, imaginaryUnit_sq]

@[simp] theorem zetaEight_pow_eight : zetaEight ^ 8 = 1 := by
  calc
    zetaEight ^ 8 = (zetaEight ^ 4) ^ 2 := by ring
    _ = 1 := by rw [zetaEight_pow_four]; ring

theorem zetaEight_ne_zero : zetaEight ≠ 0 := by
  intro h
  have := zetaEight_pow_eight
  rw [h] at this
  norm_num at this

end
end Holant.Tractable
