import Holant.Tractable.Affine
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.FinCases

/-! Exact fourth-root phase arithmetic and constructive phase witnesses for Lemma 2.6. -/

namespace Holant.Tractable

noncomputable section

@[simp] theorem imaginaryUnit_pow_three : imaginaryUnit ^ 3 = -imaginaryUnit := by
  rw [show 3 = 2 + 1 from rfl, pow_add, imaginaryUnit_sq, pow_one]
  simp

theorem imaginaryUnit_pow_mod_four (a : ℕ) :
    imaginaryUnit ^ (a % 4) = imaginaryUnit ^ a := by
  calc
    imaginaryUnit ^ (a % 4) = imaginaryUnit ^ (a % 4) *
        (imaginaryUnit ^ 4) ^ (a / 4) := by simp
    _ = imaginaryUnit ^ (a % 4 + 4 * (a / 4)) := by rw [pow_add, pow_mul]
    _ = imaginaryUnit ^ a := by rw [Nat.mod_add_div]

@[simp] theorem fourthRootPhase_one : fourthRootPhase (1 : ZMod 4) = imaginaryUnit := by
  change imaginaryUnit ^ 1 = imaginaryUnit
  exact pow_one _

@[simp] theorem fourthRootPhase_two : fourthRootPhase (2 : ZMod 4) = -1 := by
  change imaginaryUnit ^ 2 = -1
  exact imaginaryUnit_sq

@[simp] theorem fourthRootPhase_three : fourthRootPhase (3 : ZMod 4) = -imaginaryUnit := by
  change imaginaryUnit ^ 3 = -imaginaryUnit
  exact imaginaryUnit_pow_three

theorem fourthRootPhase_add (q r : ZMod 4) :
    fourthRootPhase (q + r) = fourthRootPhase q * fourthRootPhase r := by
  unfold fourthRootPhase
  rw [ZMod.val_add, imaginaryUnit_pow_mod_four, pow_add]

theorem fourthRootPhase_neg (q : ZMod 4) :
    fourthRootPhase (-q) = (fourthRootPhase q)⁻¹ := by
  apply mul_left_cancel₀ (fourthRootPhase_ne_zero q)
  rw [← fourthRootPhase_add, add_neg_cancel, fourthRootPhase_zero,
    mul_inv_cancel₀ (fourthRootPhase_ne_zero q)]

theorem fourthRootPhase_sub (q r : ZMod 4) :
    fourthRootPhase (q - r) = fourthRootPhase q / fourthRootPhase r := by
  rw [sub_eq_add_neg, fourthRootPhase_add, fourthRootPhase_neg, div_eq_mul_inv]

theorem fourthRootPhase_sum {ι : Type*} (s : Finset ι) (q : ι → ZMod 4) :
    fourthRootPhase (s.sum q) = s.prod (fun i => fourthRootPhase (q i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, fourthRootPhase_add, ih]

/-- Every genuine fourth root in the algebraic-complex field has a Z/4 phase code. -/
theorem fourthRootPhase_surjective_of_pow_four {a : AlgebraicComplex} (h : a ^ 4 = 1) :
    ∃ q : ZMod 4, fourthRootPhase q = a := by
  have hsq : (a ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using h
  rcases sq_eq_one_iff.mp hsq with hp | hp
  · rcases sq_eq_one_iff.mp hp with ha | ha
    · exact ⟨0, by simp [ha]⟩
    · exact ⟨2, by simp [ha]⟩
  · have heq : a ^ 2 = imaginaryUnit ^ 2 := hp.trans imaginaryUnit_sq.symm
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with ha | ha
    · exact ⟨1, by simp [ha]⟩
    · exact ⟨3, by simp [ha]⟩

/-- A square-one coefficient has an even phase code, exactly as required for mixed terms. -/
theorem evenPhase_of_sq_eq_one {a : AlgebraicComplex} (h : a ^ 2 = 1) :
    ∃ q : ZMod 4, (q = 0 ∨ q = 2) ∧ fourthRootPhase q = a := by
  rcases sq_eq_one_iff.mp h with ha | ha
  · exact ⟨0, Or.inl rfl, by simp [ha]⟩
  · exact ⟨2, Or.inr rfl, by simp [ha]⟩

end
end Holant.Tractable
