import Holant.Tractable.Scalars
import Mathlib.Analysis.RCLike.Sqrt

/-! Actual algebraic-complex square roots for a marked coordinate basis.
This is fixed-family algebraic data. No membership in the smaller original
coefficient field, physical realizability, or uniform algorithm is asserted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureAlgebraicSquare
open Holant.Tractable

theorem complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  simpa [Complex.sqrt] using Complex.cpow_nat_inv_pow z (n := 2) (by decide)

theorem sqrt_integral (eta : AlgebraicComplex) : IsIntegral ℚ (Complex.sqrt (eta : ℂ)) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [complex_sqrt_sq]
  exact eta.property

/-- A specified square root in the actual algebraic subfield of C. -/
def root (eta : AlgebraicComplex) : AlgebraicComplex :=
  ⟨Complex.sqrt (eta : ℂ), sqrt_integral eta⟩

@[simp] theorem root_coe (eta : AlgebraicComplex) :
    (root eta : ℂ) = Complex.sqrt (eta : ℂ) := rfl

@[simp] theorem root_sq (eta : AlgebraicComplex) : root eta ^ 2 = eta := by
  apply Subtype.ext
  exact complex_sqrt_sq (eta : ℂ)

theorem root_ne_zero (eta : AlgebraicComplex) (h : eta ≠ 0) : root eta ≠ 0 := by
  intro hz
  have hs := root_sq eta
  rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
  exact h hs.symm

/-- The actual inverse-parameter square root used by the shifted A sector. -/
def inverseRoot (eta : AlgebraicComplex) : AlgebraicComplex := root eta⁻¹

@[simp] theorem inverseRoot_sq (eta : AlgebraicComplex) :
    inverseRoot eta ^ 2 = eta⁻¹ := root_sq eta⁻¹

@[simp] theorem inverseRoot_coe (eta : AlgebraicComplex) :
    (inverseRoot eta : ℂ) = Complex.sqrt ((eta : ℂ)⁻¹) := rfl

theorem inverseRoot_ne_zero (eta : AlgebraicComplex) (h : eta ≠ 0) :
    inverseRoot eta ≠ 0 := root_ne_zero eta⁻¹ (inv_ne_zero h)

theorem exists_inverse_square (eta : AlgebraicComplex) (h : eta ≠ 0) :
    ∃ s : AlgebraicComplex, s ^ 2 = eta⁻¹ ∧ s ≠ 0 :=
  ⟨inverseRoot eta,inverseRoot_sq eta,inverseRoot_ne_zero eta h⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureAlgebraicSquare
