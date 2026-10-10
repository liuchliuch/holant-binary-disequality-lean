import Holant.Proofs.Tractability.EOEvaluation.Source
import Mathlib.Logic.Equiv.Basic


namespace Holant.LocalDrafts.Tractability.EOEvaluation.PairingCharacters
open Holant.Tractable Distribution
open scoped BigOperators
noncomputable section

structure Data (n : ℕ) where
  points : Finset (Word n)
  base : {x // x ∈ points}
  closed : ∀ a ∈ points, ∀ b ∈ points, ∀ c ∈ points, tripleXor a b c ∈ points
  central : ∀ a ∈ points, Holant.charge a = 0

variable {n : ℕ} (D : Data n)
abbrev Point := {x // x ∈ D.points}
def key (j : Fin n) : Point D → Bool := fun x => Bool.xor (x.val j) (D.base.val j)
def character (j : Fin n) (x : Point D) : ℚ := if key D j x then -1 else 1

def translate (b : Point D) : Point D ≃ Point D where
  toFun x := ⟨tripleXor D.base.val b.val x.val,
    D.closed _ D.base.property _ b.property _ x.property⟩
  invFun x := ⟨tripleXor D.base.val b.val x.val,
    D.closed _ D.base.property _ b.property _ x.property⟩
  left_inv x := by
    apply Subtype.ext; funext j
    dsimp [tripleXor]
    cases D.base.val j <;> cases b.val j <;> cases x.val j <;> rfl
  right_inv x := by
    apply Subtype.ext; funext j
    dsimp [tripleXor]
    cases D.base.val j <;> cases b.val j <;> cases x.val j <;> rfl

theorem character_mul (j : Fin n) (b x : Point D) :
    character D j (translate D b x) = character D j b * character D j x := by
  have h (a b c : Bool) :
      (if Bool.xor (Bool.xor (Bool.xor a b) c) a then (-1 : ℚ) else 1) =
        (if Bool.xor b a then (-1 : ℚ) else 1) *
          (if Bool.xor c a then (-1 : ℚ) else 1) := by
    cases a <;> cases b <;> cases c <;> norm_num
  exact h (D.base.val j) (b.val j) (x.val j)

theorem character_square (j : Fin n) (x : Point D) : character D j x * character D j x = 1 := by
  dsimp [character]; cases key D j x <;> norm_num

theorem spin_character (j : Fin n) (x : Point D) :
    spin (x.val j) = spin (D.base.val j) * character D j x := by
  have h (a b : Bool) :
      (if b then (1 : ℚ) else -1) =
        (if a then (1 : ℚ) else -1) * (if Bool.xor b a then (-1 : ℚ) else 1) := by
    cases a <;> cases b <;> norm_num
  exact h (D.base.val j) (x.val j)

def correlation (i j : Fin n) : ℚ := ∑ x : Point D, character D i x * character D j x

theorem correlation_same (i j : Fin n) (h : key D i = key D j) :
    correlation D i j = Fintype.card (Point D) := by
  have hh : character D i = character D j := by funext x; simp [character, h]
  simp [correlation, hh, character_square]

theorem correlation_distinct (i j : Fin n) (h : key D i ≠ key D j) : correlation D i j = 0 := by
  classical
  obtain ⟨b, hb⟩ := Function.ne_iff.mp h
  have hm : character D i b * character D j b = -1 := by
    dsimp [character]
    cases hi : key D i b <;> cases hj : key D j b <;> simp_all
  have he := (translate D b).sum_comp (fun x => character D i x * character D j x)
  have ht : (∑ x : Point D, character D i (translate D b x) * character D j (translate D b x)) =
      -correlation D i j := by
    simp only [character_mul]
    calc
      _ = ∑ x : Point D, (character D i b * character D j b) *
          (character D i x * character D j x) := by
        apply Finset.sum_congr rfl; intro x _; ring
      _ = _ := by simp [hm, correlation]
  change _ = correlation D i j at he
  rw [ht] at he
  linarith

theorem correlation_value (i j : Fin n) :
    correlation D i j = if key D j = key D i then (Fintype.card (Point D) : ℚ) else 0 := by
  classical
  by_cases h : key D j = key D i
  · rw [if_pos h]; exact correlation_same D i j h.symm
  · rw [if_neg h]; exact correlation_distinct D i j (Ne.symm h)

theorem central_characters (x : Point D) :
    (∑ j, spin (D.base.val j) * character D j x) = 0 := by
  simp only [← spin_character]
  rw [← charge_sum, D.central x.val x.property]
  rfl

/-- Equal normalized columns have zero total base spin. This is the
multiplicity identity from which the actual pairing is constructed. -/
theorem fiber_balance (k : Point D → Bool) :
    (∑ j : Fin n, if key D j = k then spin (D.base.val j) else 0) = 0 := by
  classical
  by_cases hk : ∃ i, key D i = k
  · obtain ⟨i, rfl⟩ := hk
    have hz : (∑ j, spin (D.base.val j) * correlation D i j) = 0 := by
      simp only [correlation, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro x _
      calc
        _ = character D i x * (∑ j, spin (D.base.val j) * character D j x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
        _ = 0 := by rw [central_characters, mul_zero]
    have he : (∑ j, spin (D.base.val j) * correlation D i j) =
        (∑ j, if key D j = key D i then spin (D.base.val j) else 0) *
          (Fintype.card (Point D) : ℚ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      rw [correlation_value]; split_ifs <;> simp
    have hn : (Fintype.card (Point D) : ℚ) ≠ 0 := by
      haveI : Nonempty (Point D) := ⟨D.base⟩
      exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Point D)))
    rw [he] at hz
    exact (mul_eq_zero.mp hz).resolve_right hn
  · have hn : ∀ j, key D j ≠ k := by intro j hj; exact hk ⟨j, hj⟩
    simp [hn]

end
end Holant.LocalDrafts.Tractability.EOEvaluation.PairingCharacters
