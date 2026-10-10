import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The arithmetic of the exceptional-orbit incidence equation.  The arguments
here use only the orders of the stabilizers and their incidence equation; no
classification of finite groups or spherical triangles is assumed. -/

namespace Holant.Projective.FiniteSubgroupClassification

/-- Convert the natural-number orbit-size equation to the rational reciprocal
equation.  Divisibility is precisely the orbit-stabilizer hypothesis needed to
interpret the natural divisions. -/
theorem spherical_incidence_of_nat {I : Type*} [Fintype I] (N : ℕ) (r : I → ℕ)
    (hN : 1 < N) (hrdvd : ∀ i, r i ∣ N)
    (hinc : (∑ i, N / r i) + 2 * (N - 1) = Fintype.card I * N) :
    ∑ i, (1 - 1 / (r i : ℚ)) = 2 - 2 / (N : ℚ) := by
  have hNpos : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
  have hq := congrArg (fun n : ℕ => (n : ℚ)) hinc
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum,
    Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] at hq
  simp_rw [Nat.cast_div_charZero (hrdvd _)] at hq
  have hsum : (∑ i, (N : ℚ) / r i) = (N : ℚ) * ∑ i, (1 : ℚ) / r i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at hq
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp [hNpos.ne']
  nlinarith

/-- A nontrivial finite projective group has two or three exceptional orbits,
once the fixed-point incidence equation has been established. -/
theorem spherical_orbit_card {I : Type*} [Fintype I] (N : ℕ) (r : I → ℕ)
    (hN : 1 < N) (hr : ∀ i, 2 ≤ r i) (hrN : ∀ i, r i ≤ N)
    (hinc : ∑ i, (1 - 1 / (r i : ℚ)) = 2 - 2 / (N : ℚ)) :
    Fintype.card I = 2 ∨ Fintype.card I = 3 := by
  have hNq : (1 : ℚ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℚ) < N := by linarith
  have hrecpos : (0 : ℚ) < 1 / (N : ℚ) := by positivity
  have hreclt : 1 / (N : ℚ) < (1 : ℚ) := (div_lt_one hNpos).2 hNq
  have hlo : (Fintype.card I : ℚ) * (1 / 2) ≤
      ∑ i, (1 - 1 / (r i : ℚ)) := by
    simpa using Finset.card_nsmul_le_sum (Finset.univ : Finset I)
      (fun i => (1 - 1 / (r i : ℚ))) (1 / 2 : ℚ) (by
        intro i _
        have hri : (2 : ℚ) ≤ r i := by exact_mod_cast hr i
        have := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 2) hri
        linarith)
  have hhi : (∑ i, (1 - 1 / (r i : ℚ))) ≤
      (Fintype.card I : ℚ) * (1 - 1 / (N : ℚ)) := by
    simpa using Finset.sum_le_card_nsmul (Finset.univ : Finset I)
      (fun i => (1 - 1 / (r i : ℚ))) (1 - 1 / (N : ℚ)) (by
        intro i _
        have hri : (0 : ℚ) < r i := by exact_mod_cast (by have := hr i; omega : 0 < r i)
        have hriN : (r i : ℚ) ≤ N := by exact_mod_cast hrN i
        have := one_div_le_one_div_of_le hri hriN
        linarith)
  rw [hinc] at hlo hhi
  simp only [div_eq_mul_inv, one_mul] at hlo hhi hrecpos hreclt
  have hlt : (Fintype.card I : ℚ) < 4 := by linarith
  have hge : (2 : ℚ) ≤ Fintype.card I := by nlinarith
  have hlt' : Fintype.card I < 4 := by exact_mod_cast hlt
  have hge' : 2 ≤ Fintype.card I := by exact_mod_cast hge
  omega

/-- In the two-orbit case every exceptional point is fixed by the entire group. -/
theorem spherical_two_orbits {I : Type*} [Fintype I] (N : ℕ) (r : I → ℕ)
    (hN : 1 < N) (hr : ∀ i, 2 ≤ r i) (hrN : ∀ i, r i ≤ N)
    (hcard : Fintype.card I = 2)
    (hinc : ∑ i, (1 - 1 / (r i : ℚ)) = 2 - 2 / (N : ℚ)) :
    ∀ i, r i = N := by
  have hNpos : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
  have hle : ∀ i ∈ (Finset.univ : Finset I),
      (1 - 1 / (r i : ℚ)) ≤ 1 - 1 / (N : ℚ) := by
    intro i _
    have hri : (0 : ℚ) < r i := by exact_mod_cast (by have := hr i; omega : 0 < r i)
    have hriN : (r i : ℚ) ≤ N := by exact_mod_cast hrN i
    have := one_div_le_one_div_of_le hri hriN
    linarith
  have heq : (∑ i, (1 - 1 / (r i : ℚ))) = ∑ _i : I, (1 - 1 / (N : ℚ)) := by
    rw [hinc]
    simp [hcard]
    ring
  have hall := (Finset.sum_eq_sum_iff_of_le hle).1 heq
  intro i
  have hi := hall i (Finset.mem_univ i)
  have hi' : (1 : ℚ) / r i = 1 / N := by linarith
  have hi'' : (r i : ℚ) = N := inv_injective (by simpa only [one_div] using hi')
  exact_mod_cast hi''

/-- The full arithmetic list for three sorted exceptional stabilizer orders.
The first alternative is the dihedral family; the other three are the
tetrahedral, octahedral and icosahedral order patterns. -/
theorem spherical_three_orders (N a b c : ℕ) (hN : 1 < N)
    (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hinc : (1 - 1 / (a : ℚ)) + (1 - 1 / (b : ℚ)) +
      (1 - 1 / (c : ℚ)) = 2 - 2 / (N : ℚ)) :
    (a = 2 ∧ b = 2 ∧ N = 2 * c) ∨
    (a = 2 ∧ b = 3 ∧ c = 3 ∧ N = 12) ∨
    (a = 2 ∧ b = 3 ∧ c = 4 ∧ N = 24) ∨
    (a = 2 ∧ b = 3 ∧ c = 5 ∧ N = 60) := by
  have hNpos : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
  have hapos : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
  have hbpos : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hcpos : (0 : ℚ) < c := by exact_mod_cast (by omega : 0 < c)
  have habq : (a : ℚ) ≤ b := by exact_mod_cast hab
  have hbcq : (b : ℚ) ≤ c := by exact_mod_cast hbc
  have hba := one_div_le_one_div_of_le hapos habq
  have hcb := one_div_le_one_div_of_le hbpos hbcq
  simp only [one_div] at hinc hba hcb
  have hNrec : (0 : ℚ) < 2 / (N : ℚ) := by positivity
  have ha2 : a = 2 := by
    by_contra h
    have ha3 : (3 : ℚ) ≤ a := by exact_mod_cast (by omega : 3 ≤ a)
    have h3 := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 3) ha3
    simp only [one_div] at h3
    linarith
  subst a
  norm_num at hinc
  have hb23 : b = 2 ∨ b = 3 := by
    have hblt : b < 4 := by
      by_contra h
      have hb4 : (4 : ℚ) ≤ b := by exact_mod_cast (by omega : 4 ≤ b)
      have h4 := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 4) hb4
      simp only [one_div] at h4
      linarith
    omega
  rcases hb23 with rfl | rfl
  · left
    refine ⟨rfl, rfl, ?_⟩
    norm_num at hinc
    field_simp at hinc
    exact_mod_cast (show (N : ℚ) = 2 * c by nlinarith)
  · have hclt : c < 6 := by
      by_contra h
      have hc6 : (6 : ℚ) ≤ c := by exact_mod_cast (by omega : 6 ≤ c)
      have h6 := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 6) hc6
      simp only [one_div] at h6
      norm_num at hinc
      linarith
    have hc345 : c = 3 ∨ c = 4 ∨ c = 5 := by omega
    rcases hc345 with rfl | rfl | rfl
    · right; left
      refine ⟨rfl, rfl, rfl, ?_⟩
      norm_num at hinc
      field_simp at hinc
      exact_mod_cast (show (N : ℚ) = 12 by nlinarith)
    · right; right; left
      refine ⟨rfl, rfl, rfl, ?_⟩
      norm_num at hinc
      field_simp at hinc
      exact_mod_cast (show (N : ℚ) = 24 by nlinarith)
    · right; right; right
      refine ⟨rfl, rfl, rfl, ?_⟩
      norm_num at hinc
      field_simp at hinc
      exact_mod_cast (show (N : ℚ) = 60 by nlinarith)

end Holant.Projective.FiniteSubgroupClassification
