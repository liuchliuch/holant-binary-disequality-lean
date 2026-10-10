import Holant.Proofs.Hardness.EOBinaryPlaneClassification
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Holant.Tractable.TwoTranslate.Phase

/-! A fixed matrix power of a full affine nonproduct binary is scalar
identity. The finite fourth-phase cases are checked algebraically; no group
classification or available gadget is assumed by this matrix lemma. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlanePower
open Holant Holant.Tractable
open scoped Matrix
namespace B
export EOBinaryPlaneClassification (Full full_affine_iff full_product_iff Cross)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
abbrev Mat := Matrix (Fin 2) (Fin 2) AlgebraicComplex

@[simp] private theorem coe_two : ((2 : AlgebraicComplex) : ℂ)=2 := rfl
@[simp] private theorem coe_four : ((4 : AlgebraicComplex) : ℂ)=4 := rfl

def normalized (r s : ZMod 4) : Mat :=
  !![1, fourthRootPhase s; fourthRootPhase r, -(fourthRootPhase r*fourthRootPhase s)]

private theorem scalar_pow (z : AlgebraicComplex) (n : ℕ) :
    (z • (1 : Mat))^n=z^n • (1 : Mat) := by
  rw [smul_pow,one_pow]

private theorem plus_eighth : (2+2*imaginaryUnit : AlgebraicComplex)^8=4096 := by
  have h : (2+2*imaginaryUnit : AlgebraicComplex)^2=8*imaginaryUnit := by
    ring_nf
    simp [imaginaryUnit_sq]
  calc
    _ = ((2+2*imaginaryUnit : AlgebraicComplex)^2)^4 := pow_mul _ 2 4
    _ = _ := by rw [h,mul_pow,imaginaryUnit_pow_four]; norm_num

private theorem minus_eighth : (2-2*imaginaryUnit : AlgebraicComplex)^8=4096 := by
  have h : (2-2*imaginaryUnit : AlgebraicComplex)^2= -8*imaginaryUnit := by
    ring_nf
    simp [imaginaryUnit_sq]
    ring
  calc
    _ = ((2-2*imaginaryUnit : AlgebraicComplex)^2)^4 := pow_mul _ 2 4
    _ = _ := by rw [h,mul_pow,imaginaryUnit_pow_four]; norm_num

theorem small_power (r s : ZMod 4) :
    normalized r s^2=(2 : AlgebraicComplex) • (1 : Mat) ∨
    normalized r s^3=(2+2*imaginaryUnit : AlgebraicComplex) • (1 : Mat) ∨
    normalized r s^3=(2-2*imaginaryUnit : AlgebraicComplex) • (1 : Mat) ∨
    normalized r s^4=(-4 : AlgebraicComplex) • (1 : Mat) := by
  rcases TwoTranslate.fourth_cases r with rfl | rfl | rfl | rfl
  all_goals rcases TwoTranslate.fourth_cases s with rfl | rfl | rfl | rfl
  · left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; right; right
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; right; left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; right; right
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; right; left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; right; right
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; right; left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; right; left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; left
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · right; right; right
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Complex.ext <;>
      norm_num [normalized, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im]

theorem normalized_power (r s : ZMod 4) :
    normalized r s^24=(4096 : AlgebraicComplex) • (1 : Mat) := by
  rcases small_power r s with h | h | h | h
  · calc
      _ = (normalized r s^2)^12 := pow_mul _ 2 12
      _ = _ := by rw [h,scalar_pow]; norm_num
  · calc
      _ = (normalized r s^3)^8 := pow_mul _ 3 8
      _ = _ := by rw [h,scalar_pow,plus_eighth]
  · calc
      _ = (normalized r s^3)^8 := pow_mul _ 3 8
      _ = _ := by rw [h,scalar_pow,minus_eighth]
  · calc
      _ = (normalized r s^4)^6 := pow_mul _ 4 6
      _ = _ := by rw [h,scalar_pow]; norm_num

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlanePower
