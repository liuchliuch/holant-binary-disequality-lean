import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! A finite algebraic selector for four-copy compression. No order, absolute
value, square roots, or hypothesis on phases is needed. The three choices are
ordered to match the literal port permutations in `ComplexNonselfdualFourCopy`.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualChoice

variable {K : Type} [Field K] [CharZero K]

def Good (t s : K) : Prop := s ≠ 0 ∧ t ^ 2 + s ^ 2 ≠ 0

private theorem good_of_zero_sum (P Q R : K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hQR : Q + R = 0) : Good Q (R + P) ∨ Good R (P + Q) := by
  classical
  by_cases hRP : R + P = 0
  · right
    have hR : R = -P := by linear_combination hRP
    have hQ' : Q = P := by linear_combination hQR - hRP
    constructor
    · intro h
      have hz : (2 : K) * P = 0 := by linear_combination h - hQ'
      exact (mul_ne_zero (by norm_num) hP) hz
    · intro h
      rw [hR, hQ'] at h
      have hz : (5 : K) * P ^ 2 = 0 := by linear_combination h
      exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 hP)) hz
  by_cases hPQ : P + Q = 0
  · left
    have hP' : P = -Q := by linear_combination hPQ
    have hR : R = -Q := by linear_combination hQR
    refine ⟨hRP, ?_⟩
    intro h
    rw [hP', hR] at h
    have hz : (5 : K) * Q ^ 2 = 0 := by linear_combination h
    exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 hQ)) hz
  by_cases hq : Q ^ 2 + (R + P) ^ 2 = 0
  · right
    refine ⟨hPQ, ?_⟩
    intro h
    have hR : R = -Q := by linear_combination hQR
    rw [hR] at hq h
    have hz : (4 : K) * P * Q = 0 := by linear_combination h - hq
    exact (mul_ne_zero (mul_ne_zero (by norm_num) hP) hQ) hz
  · exact Or.inl ⟨hRP, hq⟩

/-- The three cyclic choices cannot all fail over a characteristic-zero field. -/
theorem good_cyclic (P Q R : K) (hP : P ≠ 0) (hQ : Q ≠ 0) (hR : R ≠ 0) :
    Good P (Q + R) ∨ Good Q (R + P) ∨ Good R (P + Q) := by
  classical
  by_cases hsP : Q + R = 0
  · exact Or.inr (good_of_zero_sum P Q R hP hQ hsP)
  by_cases hsQ : R + P = 0
  · rcases good_of_zero_sum Q R P hQ hR hsQ with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  by_cases hsR : P + Q = 0
  · rcases good_of_zero_sum R P Q hR hP hsR with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  by_cases hqP : P ^ 2 + (Q + R) ^ 2 = 0
  · by_cases hqQ : Q ^ 2 + (R + P) ^ 2 = 0
    · right; right
      refine ⟨hsR, ?_⟩
      intro hqR
      have hzPQ : (2 : K) * R * (P - Q) = 0 := by
        linear_combination hqQ - hqP
      have hPQ : P = Q := sub_eq_zero.mp
        ((mul_eq_zero.mp hzPQ).resolve_left (mul_ne_zero (by norm_num) hR))
      have hzQR : (2 : K) * P * (Q - R) = 0 := by
        linear_combination hqR - hqQ
      have hQR : Q = R := sub_eq_zero.mp
        ((mul_eq_zero.mp hzQR).resolve_left (mul_ne_zero (by norm_num) hP))
      rw [hPQ, hQR] at hqP
      have hz : (5 : K) * R ^ 2 = 0 := by linear_combination hqP
      exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 hR)) hz
    · exact Or.inr (Or.inl ⟨hsQ, hqQ⟩)
  · exact Or.inl ⟨hsP, hqP⟩

/-- Index order is isolated products `[Q,P,R]`, with complementary pair sums. -/
theorem exists_choice (P Q R : K) (hP : P ≠ 0) (hQ : Q ≠ 0) (hR : R ≠ 0) :
    ∃ i : Fin 3, (![P + R, Q + R, P + Q] i) ≠ 0 ∧
      (![Q, P, R] i) ^ 2 + (![P + R, Q + R, P + Q] i) ^ 2 ≠ 0 := by
  rcases good_cyclic P Q R hP hQ hR with h | h | h
  · exact ⟨1, h⟩
  · refine ⟨0, ?_⟩
    change Good Q (P + R)
    simpa only [add_comm R P] using h
  · exact ⟨2, h⟩

/-- The first successful choice, using only the three input products. -/
def selectedIndex (P Q R : K) : Fin 3 := by
  classical
  exact if Good Q (P + R) then 0 else if Good P (Q + R) then 1 else 2

theorem selected_good (P Q R : K) (hP : P ≠ 0) (hQ : Q ≠ 0) (hR : R ≠ 0) :
    (![P + R, Q + R, P + Q] (selectedIndex P Q R)) ≠ 0 ∧
      (![Q, P, R] (selectedIndex P Q R)) ^ 2 +
        (![P + R, Q + R, P + Q] (selectedIndex P Q R)) ^ 2 ≠ 0 := by
  classical
  unfold selectedIndex
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · obtain ⟨i, hi⟩ := exists_choice P Q R hP hQ hR
    fin_cases i
    · exact False.elim (h0 hi)
    · exact False.elim (h1 hi)
    · exact hi

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualChoice
