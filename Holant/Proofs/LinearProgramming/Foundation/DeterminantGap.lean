import Holant.Proofs.Traversal.RationalLP.Codec
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Data.Nat.Factorial.Basic

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
The integer determinant gap for a nonsingular square subsystem. No subsystem,
optimal point or basis certificate is accepted by the raw LP interface. The separate BasicPoint and PositiveThreshold modules derive such a
subsystem from original feasibility and positivity. A determinant formula here is a proof, not a runtime
permutation-enumeration algorithm or a claim of polynomial LP complexity.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.DeterminantGap
open Matrix
open scoped BigOperators

def castMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  A.map (Int.castRingHom ℚ)

/-- Adjugate multiplication gives an integer numerator, even before division. -/
theorem integral_numerator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ℤ) (x : Fin n → ℚ)
    (hx : castMatrix A *ᵥ x = fun i => (b i : ℚ)) (j : Fin n) :
    (A.det : ℚ) * x j = ((A.adjugate *ᵥ b) j : ℚ) := by
  have hc : ((A.adjugate *ᵥ b) j : ℚ) =
      ((castMatrix A).adjugate *ᵥ (fun i => (b i : ℚ))) j := by
    have ha : A.adjugate.map (Int.castRingHom ℚ) = (castMatrix A).adjugate :=
      (Int.castRingHom ℚ).map_adjugate A
    calc
      ((A.adjugate *ᵥ b) j : ℚ) =
          (A.adjugate.map (Int.castRingHom ℚ) *ᵥ (fun i => (b i : ℚ))) j :=
        (Int.castRingHom ℚ).map_mulVec A.adjugate b j
      _ = _ := by rw [ha]
  calc
    (A.det : ℚ) * x j = (castMatrix A).det * x j := by
      rw [Int.cast_det]; rfl
    _ = ((castMatrix A).adjugate *ᵥ (castMatrix A *ᵥ x)) j := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      rfl
    _ = ((castMatrix A).adjugate *ᵥ (fun i => (b i : ℚ))) j := by rw [hx]
    _ = _ := hc.symm

theorem integer_abs_gap (c : ℤ) (hc : c ≠ 0) : (1 : ℚ) ≤ |(c : ℚ)| := by
  have hi : (1 : ℤ) ≤ |c| := by
    have hn := abs_nonneg c
    have he : |c| ≠ 0 := abs_ne_zero.mpr hc
    omega
  exact_mod_cast hi

/-- A positive coordinate of an integer nonsingular system is at least 1/|det|. -/
theorem positive_gap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ℤ) (x : Fin n → ℚ)
    (hx : castMatrix A *ᵥ x = fun i => (b i : ℚ)) (hd : A.det ≠ 0)
    (j : Fin n) (hj : 0 < x j) : 1 / |(A.det : ℚ)| ≤ x j := by
  have hdq : (A.det : ℚ) ≠ 0 := by exact_mod_cast hd
  have he := integral_numerator A b x hx j
  have hc : (A.adjugate *ᵥ b) j ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero] at he
    exact mul_ne_zero hdq (ne_of_gt hj) he
  have hg := integer_abs_gap _ hc
  rw [← he, abs_mul, abs_of_pos hj] at hg
  apply (div_le_iff₀ (abs_pos.mpr hdq)).mpr
  simpa only [mul_comm] using hg

def bound (n H : ℕ) : ℕ := n.factorial * H ^ n

theorem bound_le_power (n H bits : ℕ) (hH : H ≤ 2 ^ bits) :
    bound n H ≤ 2 ^ (n * n + bits * n) := by
  calc
    bound n H ≤ n ^ n * H ^ n := Nat.mul_le_mul_right _ (Nat.factorial_le_pow n)
    _ ≤ (2 ^ n) ^ n * (2 ^ bits) ^ n :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=n)).le n)
        (Nat.pow_le_pow_left hH n)
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]

/-- Leibniz's inequality supplies a bit-size bound; this is not a det program. -/
theorem determinant_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hH : ∀ i j, |A i j| ≤ (H : ℤ)) : |(A.det : ℚ)| ≤ (bound n H : ℚ) := by
  have hm : ∀ i j, |castMatrix A i j| ≤ (H : ℚ) := by
    intro i j
    change |(A i j : ℚ)| ≤ (H : ℚ)
    exact_mod_cast hH i j
  have hb := Matrix.det_le (A := castMatrix A) (abv := AbsoluteValue.abs) hm
  simpa [castMatrix, ← Int.cast_det, bound, nsmul_eq_mul] using hb

theorem positive_uniform_gap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ℤ) (x : Fin n → ℚ)
    (hx : castMatrix A *ᵥ x = fun i => (b i : ℚ)) (hd : A.det ≠ 0)
    (H : ℕ) (hH : ∀ i j, |A i j| ≤ (H : ℤ)) (j : Fin n) (hj : 0 < x j) :
    1 / (bound n H : ℚ) ≤ x j := by
  have hdq : (A.det : ℚ) ≠ 0 := by exact_mod_cast hd
  have hb := determinant_bound A H hH
  have hp : (0 : ℚ) < bound n H := (abs_pos.mpr hdq).trans_le hb
  have hg := (div_le_iff₀ (abs_pos.mpr hdq)).mp (positive_gap A b x hx hd j hj)
  apply (div_le_iff₀ hp).mpr
  exact hg.trans (mul_le_mul_of_nonneg_left hb hj.le)

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.DeterminantGap
