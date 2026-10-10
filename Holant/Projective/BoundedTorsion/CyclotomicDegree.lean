import Holant.Projective.BoundedTorsion.Arithmetic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.Tactic.ComputeDegree

/-! The degree estimate underlying source Lemma 5.2.  A primitive root whose
sum with its inverse lies in the number field has degree at most twice the
field degree.  This uses the quadratic polynomial directly, so no theorem
about maximal real cyclotomic subfields is needed. -/

namespace Holant.Projective.BoundedTorsion
open Polynomial
open scoped IntermediateField
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {L E : Type*} [Field L] [Field E] [CharZero E]
  [Algebra ℚ L] [Algebra L E] [Algebra ℚ E] [IsScalarTower ℚ L E]
  [FiniteDimensional ℚ L]

theorem minpoly_degree_le_two_of_add_inv {ζ : E} (hζ : ζ ≠ 0) {s : L}
    (hs : ζ + ζ⁻¹ = algebraMap L E s) :
    IsIntegral L ζ ∧ (minpoly L ζ).natDegree ≤ 2 := by
  let q : L[X] := X ^ 2 - C s * X + 1
  have hm : q.Monic := by dsimp [q]; monicity!
  have he : aeval ζ q = 0 := by
    simp only [q, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one]
    rw [← hs]
    field_simp
    ring
  refine ⟨⟨q, hm, he⟩, ?_⟩
  have hd : q.natDegree = 2 := by dsimp [q]; compute_degree!
  rw [← hd]
  exact natDegree_le_natDegree (minpoly.min L ζ hm he)

/-- The source's `φ(r) ≤ 2 [L:ℚ]` bound from its eigenratio identity. -/
theorem totient_le_twice_degree_of_add_inv {r : ℕ} (hr : 0 < r) {ζ : E}
    (hζ : IsPrimitiveRoot ζ r) {s : L} (hs : ζ + ζ⁻¹ = algebraMap L E s) :
    r.totient ≤ 2 * Module.finrank ℚ L := by
  have hz : ζ ≠ 0 := hζ.ne_zero hr.ne'
  obtain ⟨hI, hdegree⟩ := minpoly_degree_le_two_of_add_inv hz hs
  let A := IntermediateField.adjoin L ({ζ} : Set E)
  letI : Module ℚ A := Algebra.toModule
  letI : Module L A := Algebra.toModule
  letI : FiniteDimensional L A := IntermediateField.adjoin.finiteDimensional hI
  letI : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ L A
  let z : A := IntermediateField.AdjoinSimple.gen L ζ
  have hroot : IsPrimitiveRoot z r := by
    apply hζ.of_map_of_injective (f := A.subtype)
    exact Subtype.val_injective
  have hmin := Polynomial.cyclotomic_eq_minpoly_rat hroot hr
  have hrel : Module.finrank L A ≤ 2 := by
    rw [show Module.finrank L A = (minpoly L ζ).natDegree from
      IntermediateField.adjoin.finrank hI]
    exact hdegree
  calc
    r.totient = (minpoly ℚ z).natDegree := by rw [← hmin, natDegree_cyclotomic]
    _ ≤ Module.finrank ℚ A := minpoly.natDegree_le (A := ℚ) (B := A) z
    _ = Module.finrank ℚ L * Module.finrank L A :=
      (Module.finrank_mul_finrank ℚ L A).symm
    _ ≤ Module.finrank ℚ L * 2 := Nat.mul_le_mul_left _ hrel
    _ = 2 * Module.finrank ℚ L := Nat.mul_comm _ _

theorem eigenratio_order_dvd_exponent {r : ℕ} (hr : 0 < r) {ζ : E}
    (hζ : IsPrimitiveRoot ζ r) {s : L} (hs : ζ + ζ⁻¹ = algebraMap L E s) :
    r ∣ torsionExponent (Module.finrank ℚ L) :=
  dvd_torsionExponent hr (totient_le_twice_degree_of_add_inv hr hζ hs)

end
end Holant.Projective.BoundedTorsion
