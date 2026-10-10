import Holant.Projective.FiniteSubgroupClassification.TriangleTraces
import Holant.Projective.FiniteGroupFacts.ActualIcosahedral

/-! Literal matrix conjugacy for normalized `(2,3,5)` pairs. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section

abbrev phiC : ℂ := (goldenRatio : ℂ)
abbrev tauC : ℂ := phiC - 1

theorem phiC_sq : phiC ^ 2 = phiC + 1 := by
  change (goldenRatio : ℂ) ^ 2 = (goldenRatio : ℂ) + 1
  exact_mod_cast GoldenInt.golden_sq

theorem phiC_ne_zero : phiC ≠ 0 := by
  change (goldenRatio : ℂ) ≠ 0
  exact_mod_cast GoldenInt.golden_ne_zero

theorem tauC_ne_zero : tauC ≠ 0 := by
  intro h
  have hp : phiC = 1 := sub_eq_zero.mp h
  have := phiC_sq
  norm_num [hp] at this

theorem golden_pair_sum_sq : phiC ^ 2 + tauC ^ 2 = 3 := by
  dsimp [tauC]
  linear_combination 2 * phiC_sq

theorem golden_pair_prod : phiC * tauC = 1 := by
  dsimp [tauC]
  linear_combination phiC_sq

/-- The four possible diagonal differences, with no algebraic root assumption. -/
theorem triangle_delta_roots {d : ℂ} (hd : d ^ 4 + 3 * d ^ 2 + 1 = 0) :
    d = Complex.I * phiC ∨ d = -(Complex.I * phiC) ∨
      d = Complex.I * tauC ∨ d = -(Complex.I * tauC) := by
  have hp : phiC ^ 2 * tauC ^ 2 = 1 := by rw [← mul_pow, golden_pair_prod]; norm_num
  have hf : (d ^ 2 + phiC ^ 2) * (d ^ 2 + tauC ^ 2) = 0 := by
    calc
      _ = d ^ 4 + (phiC ^ 2 + tauC ^ 2) * d ^ 2 + phiC ^ 2 * tauC ^ 2 := by ring
      _ = 0 := by rw [golden_pair_sum_sq, hp]; exact hd
  rcases mul_eq_zero.mp hf with h | h
  · have hs : d ^ 2 = (Complex.I * phiC) ^ 2 := by
      rw [mul_pow, Complex.I_sq]
      linear_combination h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hs : d ^ 2 = (Complex.I * tauC) ^ 2 := by
      rw [mul_pow, Complex.I_sq]
      linear_combination h
    exact Or.inr (Or.inr (sq_eq_sq_iff_eq_or_eq_neg.mp hs))

theorem det_bool_formula (M : Mat) :
    Matrix.det M = M false false * M true true - M false true * M true false := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm M, Matrix.det_fin_two]
  rfl

theorem normalized_triangle_delta (U : GL2C)
    (ht : Matrix.trace (U : Mat) = 1) (hd : Matrix.det (U : Mat) = 1)
    (h5 : orderOf (zClass * pglMk ℂ U) = 5) :
    (U false false - U true true) ^ 4 + 3 * (U false false - U true true) ^ 2 + 1 = 0 := by
  have ho : orderOf (pglMk ℂ (zGL * U)) = 5 := by simpa only [map_mul, zClass] using h5
  have h := trace_quartic_of_order_five (zGL * U) ho
  have htr : Matrix.trace ((zGL * U : GL2C) : Mat) = U false false - U true true := by
    simp [Matrix.trace, Matrix.mul_apply, zGL, diagonalGL, diagonal]
    ring
  have hdet : Matrix.det ((zGL * U : GL2C) : Mat) = -1 := by
    rw [Units.val_mul, Matrix.det_mul, hd]
    norm_num [det_bool_formula, zGL, diagonalGL, diagonal]
  rw [htr, hdet] at h
  linear_combination h

/-- Normalized triangle matrices have both off-diagonal entries nonzero. -/
theorem normalized_triangle_offdiagonal (U : GL2C)
    (ht : Matrix.trace (U : Mat) = 1) (hd : Matrix.det (U : Mat) = 1)
    (h5 : orderOf (zClass * pglMk ℂ U) = 5) :
    U false true ≠ 0 ∧ U true false ≠ 0 := by
  have h := normalized_triangle_delta U ht hd h5
  have htr : U false false + U true true = 1 := by simpa [Matrix.trace, add_comm] using ht
  rw [det_bool_formula] at hd
  apply mul_ne_zero_iff.mp
  intro hz
  have hu : U false false * U true true = 1 := by simpa [hz] using hd
  have hs : (U false false - U true true) ^ 2 = -3 := by
    calc
      _ = (U false false + U true true) ^ 2 - 4 * (U false false * U true true) := by ring
      _ = -3 := by rw [htr, hu]; norm_num
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hs] at h
  norm_num at h

/-- With equal trace, determinant, and diagonal difference, nondegenerate
matrices differ by an actual diagonal conjugation. -/
theorem diagonal_conjugate_of_trace_det_delta (U V : GL2C)
    (htu : Matrix.trace (U : Mat) = 1) (htv : Matrix.trace (V : Mat) = 1)
    (hdu : Matrix.det (U : Mat) = 1) (hdv : Matrix.det (V : Mat) = 1)
    (hdelta : U false false - U true true = V false false - V true true)
    (hu : U false true ≠ 0) (hv : V false true ≠ 0) :
    ∃ t : ℂˣ, torusHom t * pglMk ℂ U * (torusHom t)⁻¹ = pglMk ℂ V := by
  have htrace : U false false + U true true = V false false + V true true := by
    simpa only [Matrix.trace, Fintype.sum_bool, Matrix.diag_apply, add_comm] using htu.trans htv.symm
  have h00 : U false false = V false false := by linear_combination (htrace + hdelta) / 2
  have h11 : U true true = V true true := by linear_combination (htrace - hdelta) / 2
  have hp : U false true * U true false = V false true * V true false := by
    rw [det_bool_formula] at hdu hdv
    rw [h00, h11] at hdu
    linear_combination hdv - hdu
  let t : ℂˣ := Units.mk0 (V false true / U false true) (div_ne_zero hv hu)
  have hinv : (diagonalGL t 1)⁻¹ = diagonalGL t⁻¹ 1 := by
    apply Units.ext
    ext i j
    cases i <;> cases j <;> simp [diagonalGL, diagonal]
  refine ⟨t, ?_⟩
  change pglMk ℂ (diagonalGL t 1) * pglMk ℂ U * (pglMk ℂ (diagonalGL t 1))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, hinv]
  congr 1
  apply Units.ext
  ext i j
  cases i <;> cases j <;>
    simp [diagonalGL, diagonal, Matrix.mul_apply, t, h00, h11]
  all_goals field_simp
  all_goals linear_combination hp

end
end Holant.Projective.FiniteSubgroupClassification
