import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.GroupTheory.OrderOfElement

/-! Effective finiteness of bounded totients, for source Lemma 5.2.
Every positive integer with totient at most `M` divides `(2*M)!`.
This proves the finite set and its common exponent without presupposing either.
The cyclotomic degree argument connecting a transfer order to this set remains
a separate theorem. -/

namespace Holant.Projective.BoundedTorsion

theorem prime_pow_le_twice_totient {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    p ^ k ≤ 2 * (p ^ k).totient := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [Nat.totient_prime_pow_succ hp, pow_succ]
  have h : p ≤ 2 * (p - 1) := by have := hp.two_le; omega
  calc
    p ^ j * p ≤ p ^ j * (2 * (p - 1)) := Nat.mul_le_mul_left _ h
    _ = 2 * (p ^ j * (p - 1)) := by ring

theorem dvd_factorial_of_totient_le {n M : ℕ} (hn : 0 < n)
    (hφ : n.totient ≤ M) : n ∣ (2 * M).factorial := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hpk
  by_cases hk : k = 0
  · simp [hk]
  have hφpk : (p ^ k).totient ≤ M :=
    (Nat.le_of_dvd (Nat.totient_pos.mpr hn) (Nat.totient_dvd_of_dvd hpk)).trans hφ
  exact Nat.dvd_factorial (pow_pos hp.pos _) <|
    (prime_pow_le_twice_totient hp (Nat.pos_of_ne_zero hk)).trans (Nat.mul_le_mul_left 2 hφpk)

theorem le_factorial_of_totient_le {n M : ℕ} (hn : 0 < n)
    (hφ : n.totient ≤ M) : n ≤ (2 * M).factorial :=
  Nat.le_of_dvd (Nat.factorial_pos _) (dvd_factorial_of_totient_le hn hφ)

theorem finite_bounded_totient (M : ℕ) : {n : ℕ | 0 < n ∧ n.totient ≤ M}.Finite := by
  apply (Set.finite_Iic ((2 * M).factorial)).subset
  intro n hn
  exact le_factorial_of_totient_le hn.1 hn.2

/-- Explicit finite search space for the source's admissible projective orders. -/
def admissibleOrders (D : ℕ) : Finset ℕ :=
  (Finset.range ((4 * D).factorial + 1)).filter (fun r => 0 < r ∧ r.totient ≤ 2 * D)

theorem mem_admissibleOrders {r D : ℕ} :
    r ∈ admissibleOrders D ↔ 0 < r ∧ r.totient ≤ 2 * D := by
  simp only [admissibleOrders, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have hb := le_factorial_of_totient_le h.1 h.2
    have he : 2 * (2 * D) = 4 * D := by omega
    rw [he] at hb
    omega

/-- The computable least common multiple in the source proof. -/
def torsionExponent (D : ℕ) : ℕ := (admissibleOrders D).lcm id

theorem torsionExponent_pos (D : ℕ) : 0 < torsionExponent D := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro r hr
  exact (mem_admissibleOrders.mp hr).1.ne'

theorem dvd_torsionExponent {r D : ℕ} (hr : 0 < r) (hφ : r.totient ≤ 2 * D) :
    r ∣ torsionExponent D :=
  Finset.dvd_lcm (mem_admissibleOrders.mpr ⟨hr, hφ⟩)

/-- Once the eigenratio degree estimate is proved, all torsion orders have
one common exponent.  This is only the arithmetic implication, not the
number-field torsion theorem. -/
theorem pow_torsionExponent {G : Type*} [Monoid G] {g : G} {D : ℕ}
    (hg : IsOfFinOrder g) (hφ : (orderOf g).totient ≤ 2 * D) :
    g ^ torsionExponent D = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (dvd_torsionExponent hg.orderOf_pos hφ)

end Holant.Projective.BoundedTorsion
