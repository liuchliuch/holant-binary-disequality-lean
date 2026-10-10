import Holant.Tractable.SymmetricBinaryPullback.LocalAffine
import Holant.Tractable.AffinePhaseCriterion
import Holant.Tractable.Conformal.MatrixSupport
import Mathlib.Tactic.LinearCombination

/-! Necessary phase identities obtained from the actual selected local twists. -/
namespace Holant.EightVertex.LocalAffineCollapse.Phase
open Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev W := Fin 4 → Bool

def overlap (s x : W) : ℕ := ∑ j, if s j && x j then 1 else 0

def twistCoefficient (s x : W) : AlgebraicComplex :=
  ∏ j, if s j && x j then zetaEight else 1

theorem twistCoefficient_ne_zero (s x : W) : twistCoefficient s x ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  split <;> simp [zetaEight_ne_zero]

theorem twistCoefficient_eq (s x : W) :
    twistCoefficient s x = zetaEight ^ overlap s x := by
  unfold twistCoefficient overlap
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  split <;> simp_all

theorem twist_apply (s : W) (f : Signature AlgebraicComplex 4) (x : W) :
    localTwist s f x = twistCoefficient s x * f x := localTwist_apply s f x

theorem twist_nonzero_iff (s : W) (f : Signature AlgebraicComplex 4) (x : W) :
    localTwist s f x ≠ 0 ↔ f x ≠ 0 := by
  rw [twist_apply, mul_ne_zero_iff]
  simp [twistCoefficient_ne_zero]

theorem twistCoefficient_complement_self (s : W) :
    twistCoefficient s (complementWord s) = 1 := by
  unfold twistCoefficient
  have h (j : Fin 4) : (s j && complementWord s j) = false := by
    cases h : s j <;> simp [complementWord, h]
  simp [h]

theorem twistCoefficient_self_four (s : W) :
    twistCoefficient s s ^ 4 = (-1 : AlgebraicComplex) ^ Holant.weight s := by
  rw [twistCoefficient_eq, ← pow_mul, Nat.mul_comm, pow_mul, zetaEight_pow_four]
  congr 1
  unfold overlap Holant.weight
  simp

/-- Every affine phase gives a square cross relation on any complement rectangle.
Only its four corners need to lie in the support. -/
theorem affine_complement_cross_square (f : Signature AlgebraicComplex 4)
    (hf : Affine f) (s t : W) (hs : f s ≠ 0) (ht : f t ≠ 0)
    (hsc : f (complementWord s) ≠ 0) (htc : f (complementWord t) ≠ 0) :
    (f s * f (complementWord t)) ^ 2 = (f (complementWord s) * f t) ^ 2 := by
  rcases hf with rfl | ⟨a, ha, S, Q, rfl⟩
  · exact False.elim (hs rfl)
  have hholds (x : W) (hx : affineFormula a S Q x ≠ 0) : S.Holds x := by
    by_contra h
    exact hx (by simp [affineFormula, h])
  have hs' := hholds s hs
  have ht' := hholds t ht
  have hsc' := hholds (complementWord s) hsc
  have htc' := hholds (complementWord t) htc
  have hc := quadratic_phase_cross Q s (fun _ => true) (xor s t) (fun _ => true)
  have h1 : xor s (fun _ => true) = complementWord s := by
    funext j; simp only [xor_apply, complementWord]; cases s j <;> rfl
  have h2 : xor (xor s (fun _ => true)) (xor s t) = complementWord t := by
    funext j; simp only [xor_apply, complementWord]; cases s j <;> cases t j <;> rfl
  have h3 : xor (complementWord t) (fun _ => true) = t := by
    funext j; simp only [xor_apply, complementWord]; cases t j <;> rfl
  have h4 : xor t (fun _ => true) = complementWord t := by
    funext j; simp only [xor_apply, complementWord]; cases t j <;> rfl
  rw [h2, h3, xor_cancel_right, xor_cancel_left, h1, h4] at hc
  simp only [affineFormula, ite_eq_left hs', ite_eq_left ht', ite_eq_left hsc', ite_eq_left htc']
  linear_combination -a ^ 4 * hc

theorem pow_mod_eight (rho : AlgebraicComplex) (hr : rho ^ 8 = 1) (m : ℕ) :
    rho ^ m = rho ^ (m % 8) := by
  conv_lhs => rw [← Nat.mod_add_div m 8, pow_add, pow_mul, hr, one_pow, mul_one]

theorem weight_complement_mod_four : ∀ s : W,
    (4 * Holant.weight (complementWord s)) % 8 = (4 * Holant.weight s) % 8 := by
  decide

theorem weight_complement_mod_two : ∀ s : W, Holant.weight s % 2 = 0 →
    (2 * Holant.weight (complementWord s)) % 8 = (2 * Holant.weight s) % 8 := by
  decide

theorem weight_eq (s : W) : Holant.weight s = ∑ j, if s j then 1 else 0 := rfl

end
end Holant.EightVertex.LocalAffineCollapse.Phase
