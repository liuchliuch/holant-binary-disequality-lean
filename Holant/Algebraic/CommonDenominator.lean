import Holant.Algebraic.RationalHeight
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Int.NatAbs

/-!
# Common denominators for exponentially many fixed-degree terms

Unlike a repeated arbitrary rational-addition bound, the theorem here preserves
one denominator across every monomial. The resulting bit bound is logarithmic
in the number of summands and linear in their degree. This is the scalar rational
part of the paper's fixed-coefficient-field output-size argument; translating an
arbitrary number-field basis multiplication into such scalar monomials is still
separate work.
-/

namespace Holant.Algebraic

open scoped BigOperators

/-- A concrete common denominator for any fixed finite rational table. -/
def commonDenominator {ι : Type*} [Fintype ι] (f : ι → ℚ) : ℕ :=
  ∏ i, (f i).den

theorem commonDenominator_pos {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    0 < commonDenominator f := Finset.prod_pos (fun i _ => (f i).den_pos)

theorem den_dvd_commonDenominator {ι : Type*} [Fintype ι] (f : ι → ℚ) (i : ι) :
    (f i).den ∣ commonDenominator f := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- Exact integer numerator after clearing the fixed common denominator. -/
def clearedNumerator {ι : Type*} [Fintype ι] (f : ι → ℚ) (i : ι) : ℤ :=
  (f i).num * ((commonDenominator f / (f i).den : ℕ) : ℤ)

theorem clearedNumerator_correct {ι : Type*} [Fintype ι] (f : ι → ℚ) (i : ι) :
    (clearedNumerator f i : ℚ) / commonDenominator f = f i := by
  have h := Nat.mul_div_cancel' (den_dvd_commonDenominator f i)
  have hc : ((f i).den : ℚ) * (commonDenominator f / (f i).den : ℕ) = commonDenominator f := by
    exact_mod_cast h
  rw [clearedNumerator, Int.cast_mul, Int.cast_natCast, ← hc]
  rw [mul_div_mul_right]
  · exact Rat.num_div_den (f i)
  · have hp : 0 < commonDenominator f / (f i).den := by
      apply Nat.div_pos
      · exact Nat.le_of_dvd (commonDenominator_pos f) (den_dvd_commonDenominator f i)
      · exact (f i).den_pos
    exact_mod_cast hp.ne'

/-- A computable uniform numerator bound for the fixed table. -/
def familyNumeratorBound {ι : Type*} [Fintype ι] (f : ι → ℚ) : ℕ :=
  ∑ i, (clearedNumerator f i).natAbs

theorem clearedNumerator_le {ι : Type*} [Fintype ι] (f : ι → ℚ) (i : ι) :
    (clearedNumerator f i).natAbs ≤ familyNumeratorBound f := by
  unfold familyNumeratorBound
  exact Finset.single_le_sum (f := fun j => (clearedNumerator f j).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Sum of monomials of equal degree with one positive common denominator. -/
def rationalSumProducts (L k D : ℕ) (a : Fin L → Fin k → ℤ) : ℚ :=
  ∑ t, ∏ i, (a t i : ℚ) / D

/-- The exponentially large sum does not multiply its denominator per summand. -/
theorem rationalSumProducts_eq (L k D : ℕ) (a : Fin L → Fin k → ℤ) :
    rationalSumProducts L k D a =
      ((∑ t, ∏ i, a t i : ℤ) : ℚ) / (D ^ k : ℕ) := by
  simp only [rationalSumProducts, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Int.cast_sum, Int.cast_prod, Nat.cast_pow,
    Finset.sum_div]

/-- Integer numerators grow with the number of summands and product degree. -/
theorem sumProducts_numerator_le {L k M : ℕ} (a : Fin L → Fin k → ℤ)
    (h : ∀ t i, (a t i).natAbs ≤ M) :
    (∑ t, ∏ i, a t i : ℤ).natAbs ≤ L * M ^ k := by
  calc
    (∑ t, ∏ i, a t i : ℤ).natAbs ≤ ∑ t, (∏ i, a t i : ℤ).natAbs :=
      Int.natAbs_sum_le _ _
    _ = ∑ t, ∏ i, (a t i).natAbs := by
      change (∑ t, Int.natAbsHom (∏ i, a t i)) = ∑ t, ∏ i, Int.natAbsHom (a t i)
      simp only [map_prod]
    _ ≤ ∑ _t : Fin L, M ^ k := by
      apply Finset.sum_le_sum
      intro t _
      calc
        (∏ i, (a t i).natAbs) ≤ ∏ _i : Fin k, M := Finset.prod_le_prod (fun i _ => h t i)
        _ = M ^ k := by simp
    _ = L * M ^ k := by simp

/-- Both canonical numerator and denominator are controlled after cancellation. -/
theorem rationalSumProducts_height_le {L k D M : ℕ} (hD : 0 < D)
    (a : Fin L → Fin k → ℤ) (h : ∀ t i, (a t i).natAbs ≤ M) :
    rationalHeight (rationalSumProducts L k D a) ≤ max (L * M ^ k) (D ^ k) := by
  rw [rationalSumProducts_eq]
  have hd : ((D ^ k : ℕ) : ℤ) ≠ 0 := by positivity
  have hn := divInt_num_le (∑ t, ∏ i, a t i) ((D ^ k : ℕ) : ℤ) hd
  have hden := divInt_den_le (∑ t, ∏ i, a t i) ((D ^ k : ℕ) : ℤ) hd
  rw [Rat.divInt_eq_div] at hn hden
  simp only [Int.cast_natCast, Int.natAbs_natCast] at hn hden
  exact max_le_max (le_trans hn (sumProducts_numerator_le a h)) hden

/-- Natural powers have bit length linear in their exponent. -/
theorem natSize_pow_le (a k : ℕ) : (a ^ k).size ≤ k * a.size + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := natSize_mul_le (a ^ k) a
    rw [pow_succ]
    calc
      (a ^ k * a).size ≤ (a ^ k).size + a.size := h
      _ ≤ k * a.size + 1 + a.size := Nat.add_le_add_right ih _
      _ = (k + 1) * a.size + 1 := by simp only [Nat.add_mul, Nat.one_mul]; omega

/-- The key scalar size estimate: logarithmic in the summand count and linear in
product degree, with fixed coefficient constants. -/
theorem rationalSumProducts_bitHeight_le {L k D M : ℕ} (hD : 0 < D)
    (a : Fin L → Fin k → ℤ) (h : ∀ t i, (a t i).natAbs ≤ M) :
    rationalBitHeight (rationalSumProducts L k D a) ≤
      L.size + k * max M.size D.size + 1 := by
  have hn := le_trans (natSize_mul_le L (M ^ k))
    (Nat.add_le_add_left (natSize_pow_le M k) L.size)
  have hd := natSize_pow_le D k
  have hm := Nat.mul_le_mul_left k (le_max_left M.size D.size)
  have hD' := Nat.mul_le_mul_left k (le_max_right M.size D.size)
  apply le_trans (Nat.size_le_size (rationalSumProducts_height_le hD a h))
  apply Nat.size_le.mpr
  apply max_lt
  · apply Nat.size_le.mp
    omega
  · apply Nat.size_le.mp
    omega

/-- Actual faithful binary output length inherits the common-denominator bound. -/
theorem rationalSumProducts_encoded_length_le {L k D M : ℕ} (hD : 0 < D)
    (a : Fin L → Fin k → ℤ) (h : ∀ t i, (a t i).natAbs ≤ M) :
    (rationalEncoding.encode (rationalSumProducts L k D a)).length ≤
      2 * (L.size + k * max M.size D.size + 2) := by
  apply le_trans (rationalEncoding_length_le_height _)
  have hb := rationalSumProducts_bitHeight_le hD a h
  omega

/-- Specialize the bound to any fixed finite rational signature-coefficient table.
The common denominator and numerator bound are computed from that table. -/
theorem finiteFamily_sumProducts_length_le {ι : Type*} [Fintype ι]
    (f : ι → ℚ) {L k : ℕ} (labels : Fin L → Fin k → ι) :
    (rationalEncoding.encode (∑ t, ∏ i, f (labels t i))).length ≤
      2 * (L.size + k * max (familyNumeratorBound f).size (commonDenominator f).size + 2) := by
  have he : (∑ t, ∏ i, f (labels t i)) =
      rationalSumProducts L k (commonDenominator f)
        (fun t i => clearedNumerator f (labels t i)) := by
    simp only [rationalSumProducts, clearedNumerator_correct]
  rw [he]
  exact rationalSumProducts_encoded_length_le (commonDenominator_pos f) _
    (fun t i => clearedNumerator_le f (labels t i))

/-- Exponentially many degree-`k` terms have output bit length linear in the
logarithmic term bound `e` and in `k`, for one fixed finite coefficient table. -/
theorem finiteFamily_sumProducts_length_le_exponential {ι : Type*} [Fintype ι]
    (f : ι → ℚ) {L k e : ℕ} (labels : Fin L → Fin k → ι) (hL : L ≤ 2 ^ e) :
    (rationalEncoding.encode (∑ t, ∏ i, f (labels t i))).length ≤
      2 * (e + k * max (familyNumeratorBound f).size (commonDenominator f).size + 3) := by
  have h := finiteFamily_sumProducts_length_le f labels
  have hsize := Nat.size_le_size hL
  rw [Nat.size_pow] at hsize
  omega

end Holant.Algebraic
