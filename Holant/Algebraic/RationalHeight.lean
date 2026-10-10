import Holant.Algebraic.EncodingSize
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Positivity

/-!
# Rational coefficient growth

The height is the maximum of the absolute canonical numerator and the positive
canonical denominator. Exact addition and multiplication obey explicit height
bounds; the corresponding binary-height bounds control encoded answer length.
These are arithmetic size bounds, not Turing-machine runtime proofs.
-/

namespace Holant.Algebraic

/-- Multiplicative coordinate height, always at least one. -/
def rationalHeight (q : ℚ) : ℕ := max q.num.natAbs q.den

theorem rationalHeight_pos (q : ℚ) : 0 < rationalHeight q :=
  lt_of_lt_of_le q.den_pos (le_max_right _ _)

/-- Cancelling a fraction cannot increase its numerator magnitude. -/
theorem divInt_num_le (n d : ℤ) (hd : d ≠ 0) : (Rat.divInt n d).num.natAbs ≤ n.natAbs := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd n hd) hn

/-- Cancelling a fraction cannot increase its positive denominator. -/
theorem divInt_den_le (n d : ℤ) (hd : d ≠ 0) : (Rat.divInt n d).den ≤ d.natAbs := by
  simpa using Int.natAbs_le_of_dvd_ne_zero (Rat.den_dvd n d) hd

theorem rational_mul_num_le (q r : ℚ) :
    (q * r).num.natAbs ≤ q.num.natAbs * r.num.natAbs := by
  rw [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt]
  simpa [Int.natAbs_mul] using divInt_num_le (q.num * r.num) (q.den * r.den) (by positivity)

theorem rational_mul_den_le (q r : ℚ) : (q * r).den ≤ q.den * r.den :=
  Nat.le_of_dvd (Nat.mul_pos q.den_pos r.den_pos) (Rat.mul_den_dvd q r)

theorem rational_add_num_le (q r : ℚ) :
    (q + r).num.natAbs ≤ q.num.natAbs * r.den + q.den * r.num.natAbs := by
  rw [Rat.add_num_den]
  apply le_trans (divInt_num_le _ _ (by positivity))
  simpa [Int.natAbs_mul] using Int.natAbs_add_le (q.num * r.den) (q.den * r.num)

theorem rational_add_den_le (q r : ℚ) : (q + r).den ≤ q.den * r.den :=
  Nat.le_of_dvd (Nat.mul_pos q.den_pos r.den_pos) (Rat.add_den_dvd q r)

theorem rationalHeight_mul (q r : ℚ) :
    rationalHeight (q * r) ≤ rationalHeight q * rationalHeight r := by
  apply max_le
  · exact le_trans (rational_mul_num_le q r)
      (Nat.mul_le_mul (le_max_left _ _) (le_max_left _ _))
  · exact le_trans (rational_mul_den_le q r)
      (Nat.mul_le_mul (le_max_right _ _) (le_max_right _ _))

theorem rationalHeight_add (q r : ℚ) :
    rationalHeight (q + r) ≤ 2 * rationalHeight q * rationalHeight r := by
  have ha := Nat.mul_le_mul (le_max_left q.num.natAbs q.den) (le_max_right r.num.natAbs r.den)
  have hb := Nat.mul_le_mul (le_max_right q.num.natAbs q.den) (le_max_left r.num.natAbs r.den)
  have hd := Nat.mul_le_mul (le_max_right q.num.natAbs q.den) (le_max_right r.num.natAbs r.den)
  unfold rationalHeight
  rw [Nat.mul_assoc]
  apply max_le
  · have h := rational_add_num_le q r
    omega
  · have h := rational_add_den_le q r
    omega

/-- Binary height, not a unary magnitude cost. -/
def rationalBitHeight (q : ℚ) : ℕ := (rationalHeight q).size

theorem natSize_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  calc
    a * b ≤ 2 ^ a.size * b := Nat.mul_le_mul_right b (Nat.lt_size_self a).le
    _ < 2 ^ a.size * 2 ^ b.size :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity)
    _ = 2 ^ (a.size + b.size) := (pow_add _ _ _).symm

theorem rationalBitHeight_mul (q r : ℚ) :
    rationalBitHeight (q * r) ≤ rationalBitHeight q + rationalBitHeight r :=
  le_trans (Nat.size_le_size (rationalHeight_mul q r)) (natSize_mul_le _ _)

theorem rationalBitHeight_add (q r : ℚ) :
    rationalBitHeight (q + r) ≤ rationalBitHeight q + rationalBitHeight r + 2 := by
  have h := le_trans (Nat.size_le_size (rationalHeight_add q r))
    (natSize_mul_le (2 * rationalHeight q) (rationalHeight r))
  have htwo := natSize_mul_le 2 (rationalHeight q)
  rw [show Nat.size 2 = 2 from rfl] at htwo
  unfold rationalBitHeight
  omega

/-- The actual rational bitstring has at most twice binary height plus a
small constant. -/
theorem rationalEncoding_length_le_height (q : ℚ) :
    (rationalEncoding.encode q).length ≤ 2 * (rationalBitHeight q + 1) := by
  apply le_trans (rationalEncoding_length_le q)
  apply Nat.mul_le_mul_left
  apply max_le
  · exact Nat.add_le_add_right (Nat.size_le_size (le_max_left _ _)) 1
  · exact le_trans (Nat.size_le_size (le_max_right _ _)) (Nat.le_succ _)

end Holant.Algebraic
