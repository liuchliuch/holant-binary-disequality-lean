import Holant.Proofs.Traversal.RationalLP.Codec
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Exact downward grid rounding and row residual bounds. These are mathematical
sublemmas, not an LP solver or a claim that rounding preserves equalities.
The grid denominator is explicit; its eventual algorithmic choice and bit
bound must be proved by the LP algorithm, not supplied as a correctness input.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Precision
open scoped BigOperators

def down (h : ℕ) (q : ℚ) : ℚ := (⌊q * (h : ℚ)⌋ : ℚ) / (h : ℚ)

theorem down_le (h : ℕ) (hh : 0 < h) (q : ℚ) : down h q ≤ q := by
  have hp : (0 : ℚ) < h := by exact_mod_cast hh
  exact (div_le_iff₀ hp).mpr (Int.floor_le _)

theorem lt_down_add (h : ℕ) (hh : 0 < h) (q : ℚ) : q < down h q + 1 / (h : ℚ) := by
  have hp : (0 : ℚ) < h := by exact_mod_cast hh
  unfold down
  rw [← add_div, lt_div_iff₀ hp]
  exact Int.lt_floor_add_one _

theorem error (h : ℕ) (hh : 0 < h) (q : ℚ) : |down h q - q| < 1 / (h : ℚ) := by
  rw [abs_of_nonpos (sub_nonpos.mpr (down_le h hh q))]
  linarith [lt_down_add h hh q]

theorem down_nonneg (h : ℕ) (hh : 0 < h) {q : ℚ} (hq : 0 ≤ q) : 0 ≤ down h q := by
  apply div_nonneg
  · exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hq (by positivity : (0 : ℚ) ≤ h))
  · positivity

theorem down_mem_unit (h : ℕ) (hh : 0 < h) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1) :
    0 ≤ down h q ∧ down h q ≤ 1 :=
  ⟨down_nonneg h hh hq.1, (down_le h hh q).trans hq.2⟩

/-- The actual integer numerator of a rounded unit-box point is at most h. -/
theorem grid_numerator (h : ℕ) (hh : 0 < h) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1) :
    0 ≤ ⌊q * (h : ℚ)⌋ ∧ ⌊q * (h : ℚ)⌋ ≤ (h : ℤ) := by
  have hn : (0 : ℚ) ≤ h := by positivity
  refine ⟨Int.floor_nonneg.mpr (mul_nonneg hq.1 hn), ?_⟩
  have hf := (Int.floor_le (q * (h : ℚ))).trans (mul_le_of_le_one_left hn hq.2)
  exact_mod_cast hf

theorem row_error {n : ℕ} (a : Fin n → ℤ) (x : Fin n → ℚ)
    (h : ℕ) (hh : 0 < h) :
    |(∑ j, (a j : ℚ) * down h (x j)) - ∑ j, (a j : ℚ) * x j| ≤
      (∑ j, |(a j : ℚ)|) / (h : ℚ) := by
  calc
    _ = |∑ j, (a j : ℚ) * (down h (x j) - x j)| := by
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ j, |(a j : ℚ) * (down h (x j) - x j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |(a j : ℚ)| * (1 / (h : ℚ)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (error h hh (x j)).le (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- This yields an approximate equality only, even when x is exactly feasible. -/
theorem feasible_row_error (d : Codec.Raw) (x : Fin d.dimension → ℚ)
    (hx : Codec.Feasible d x) (h : ℕ) (hh : 0 < h) (i : Fin d.rowCount) :
    |(∑ j, (d.coefficient i j : ℚ) * down h (x j)) - (d.constant i : ℚ)| ≤
      (∑ j, |(d.coefficient i j : ℚ)|) / (h : ℚ) := by
  rw [← hx.1 i]
  exact row_error _ _ h hh

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Precision
