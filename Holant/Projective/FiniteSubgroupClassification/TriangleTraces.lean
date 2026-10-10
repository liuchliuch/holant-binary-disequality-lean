import Holant.Projective.FiniteSubgroupClassification.KleinConjugacy

/-! Trace equations for the actual projective `(2,3,5)` triangle generators.
They follow from scalar powers and distinct characteristic roots, with no
representation-classification assumption. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

theorem eigenvalue_powers_eq_of_projective_order (U : GL2C) (n : ℕ)
    (ho : orderOf (pglMk ℂ U) = n) {a b : ℂ}
    (ha : a ∈ spectrum ℂ (U : Mat)) (hb : b ∈ spectrum ℂ (U : Mat)) : a ^ n = b ^ n := by
  have he : pglMk ℂ (U ^ n) = pglMk ℂ 1 := by
    rw [map_pow, map_one, ← ho, pow_orderOf_eq_one]
  obtain ⟨c, _, hc⟩ := projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp he)
  exact (eigenvalue_pow_of_scalar_pow ha hc).trans (eigenvalue_pow_of_scalar_pow hb hc).symm

/-- A projective element of order three satisfies `tr² = det` on every representative. -/
theorem trace_sq_eq_det_of_order_three (U : GL2C) (ho : orderOf (pglMk ℂ U) = 3) :
    Matrix.trace (U : Mat) ^ 2 = Matrix.det (U : Mat) := by
  have hf : IsOfFinOrder (pglMk ℂ U) := orderOf_pos_iff.mp (by omega)
  have hn : pglMk ℂ U ≠ 1 := by intro h; simp [h] at ho
  obtain ⟨a, b, _, _, hab, htr, hdet, ha, hb⟩ := exists_distinct_eigenpair U hf hn
  have hp := eigenvalue_powers_eq_of_projective_order U 3 ho ha hb
  have hz : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by linear_combination hp
  have hsum := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)
  rw [htr, hdet]
  linear_combination hsum

/-- The projective order-five trace/determinant equation. -/
theorem trace_quartic_of_order_five (U : GL2C) (ho : orderOf (pglMk ℂ U) = 5) :
    Matrix.trace (U : Mat) ^ 4 - 3 * Matrix.trace (U : Mat) ^ 2 * Matrix.det (U : Mat) +
      Matrix.det (U : Mat) ^ 2 = 0 := by
  have hf : IsOfFinOrder (pglMk ℂ U) := orderOf_pos_iff.mp (by omega)
  have hn : pglMk ℂ U ≠ 1 := by intro h; simp [h] at ho
  obtain ⟨a, b, _, _, hab, htr, hdet, ha, hb⟩ := exists_distinct_eigenpair U hf hn
  have hp := eigenvalue_powers_eq_of_projective_order U 5 ho ha hb
  have hz : (a - b) * (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) = 0 := by
    linear_combination hp
  have hsum := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)
  rw [htr, hdet]
  linear_combination hsum

/-- An order-three projective class admits an actual trace-one, determinant-one representative. -/
theorem exists_trace_one_rep_of_order_three (q : PGL2 ℂ) (ho : orderOf q = 3) :
    ∃ U : GL2C, pglMk ℂ U = q ∧ Matrix.trace (U : Mat) = 1 ∧ Matrix.det (U : Mat) = 1 := by
  induction q using Quotient.inductionOn with
  | h U =>
    have ht := trace_sq_eq_det_of_order_three U ho
    have htr : Matrix.trace (U : Mat) ≠ 0 := by
      intro h
      exact U.det_ne_zero (by rw [← ht, h]; simp)
    let c : ℂˣ := Units.mk0 (Matrix.trace (U : Mat))⁻¹ (inv_ne_zero htr)
    let V : GL2C := Matrix.GeneralLinearGroup.scalar Bool c * U
    have hv : (V : Mat) = (Matrix.trace (U : Mat))⁻¹ • (U : Mat) := by
      dsimp [V]
      rw [← Matrix.smul_eq_diagonal_mul]
      rfl
    refine ⟨V, ?_, ?_, ?_⟩
    · apply pglMk_eq_iff_projectiveClass_eq.mpr
      exact projectiveClass_eq_iff.mpr ⟨_, inv_ne_zero htr, hv⟩
    · rw [hv, Matrix.trace_smul]
      exact inv_mul_cancel₀ htr
    · rw [hv, Matrix.det_smul, Fintype.card_bool, ← ht]
      field_simp

end
end Holant.Projective.FiniteSubgroupClassification
