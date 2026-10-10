import Holant.Algebraic.FixedFamilySize
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! Task-local adaptation, pending independent Lean validation.
An explicit rational linear retraction of the unit line in the ORIGINAL fixed
basis. No coordinate is selected by runtime choice. The computational data are
only unitCode and its fixed rational sum of squares; the semantic basis is used
solely in the correctness proof. General field elements have a total specified
output, without pretending that they all represent integers.
-/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder

open Holant.Algebraic
open scoped BigOperators

namespace Coordinates
variable {n : ℕ}

def norm (D : ArithmeticData n) : ℚ := ∑ i, (D.unitCode i) ^ 2
def weighted (D : ArithmeticData n) (v : Fin n → ℚ) : ℚ := ∑ i, v i * D.unitCode i
def rational (D : ArithmeticData n) (v : Fin n → ℚ) : ℚ := weighted D v * (norm D)⁻¹
def integer (D : ArithmeticData n) (v : Fin n → ℚ) : ℤ := (rational D v).num
def natural (D : ArithmeticData n) (v : Fin n → ℚ) : ℕ := (integer D v).toNat

variable {K : Type} [Field K] [Algebra ℚ K]

/-- Existence is proved from decode_unit and injectivity, not supplied to the
machine. In particular a zero-dimensional presentation is impossible. -/
theorem unit_coordinate_exists (F : FixedField K n) : ∃ i, F.unitCode i ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hz : F.unitCode = 0 := funext h
  have he : (1 : K) = 0 := by
    rw [← F.decode_unit, hz]
    exact F.decode.map_zero
  exact one_ne_zero he

theorem norm_pos (F : FixedField K n) : 0 < norm F.toArithmeticData := by
  obtain ⟨i, hi⟩ := unit_coordinate_exists F
  exact Finset.sum_pos' (fun j _ => sq_nonneg (F.unitCode j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem norm_ne_zero (F : FixedField K n) : norm F.toArithmeticData ≠ 0 :=
  ne_of_gt (norm_pos F)

theorem weighted_unit (D : ArithmeticData n) (q : ℚ) :
    weighted D (q • D.unitCode) = q * norm D := by
  unfold weighted norm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem rational_unit (F : FixedField K n) (q : ℚ) :
    rational F.toArithmeticData (q • F.unitCode) = q := by
  unfold rational
  rw [weighted_unit, mul_assoc, mul_inv_cancel₀ (norm_ne_zero F), mul_one]

theorem integer_unit (F : FixedField K n) (z : ℤ) :
    integer F.toArithmeticData ((z : ℚ) • F.unitCode) = z := by
  simp [integer, rational_unit]

theorem natural_unit (F : FixedField K n) (m : ℕ) :
    natural F.toArithmeticData ((m : ℚ) • F.unitCode) = m := by
  simp [natural, integer, rational_unit]

/-- The inverse-basis coordinates of a rational scalar are forced by the
linear equivalence. This is a theorem about the existing codec, not a decoder
correctness premise or an executable field operation. -/
theorem coordinates_algebraMap (F : FixedField K n) (q : ℚ) :
    F.decode.symm (algebraMap ℚ K q) = q • F.unitCode := by
  apply F.decode.injective
  rw [F.decode.apply_symm_apply, map_smul, F.decode_unit]
  simp [Algebra.smul_def]

theorem coordinates_natCast (F : FixedField K n) (m : ℕ) :
    F.decode.symm (m : K) = (m : ℚ) • F.unitCode := by
  simpa using coordinates_algebraMap F (m : ℚ)

theorem coordinates_intCast (F : FixedField K n) (z : ℤ) :
    F.decode.symm (z : K) = (z : ℚ) • F.unitCode := by
  simpa using coordinates_algebraMap F (z : ℚ)

end Coordinates

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder
