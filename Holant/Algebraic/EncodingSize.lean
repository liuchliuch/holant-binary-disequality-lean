import Holant.Algebraic.RationalEncoding
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Proven bit-length bounds for the exact codecs

These bounds concern the actual binary strings, not unary numeric magnitude.
They establish that pairing/framing the canonical rational coefficients has only
linear overhead in their numerator/denominator bit lengths. Arithmetic growth and
Turing-machine arithmetic runtimes are separate obligations.
-/

namespace Holant.Algebraic

open Computability

theorem encodePosNum_length (n : PosNum) : (encodePosNum n).length = n.natSize := by
  induction n with
  | one => rfl
  | bit0 n ih => simpa [encodePosNum, PosNum.natSize] using congrArg Nat.succ ih
  | bit1 n ih => simpa [encodePosNum, PosNum.natSize] using congrArg Nat.succ ih

theorem encodeNum_length (n : Num) : (encodeNum n).length = Nat.size (n : ℕ) := by
  cases n with
  | zero => rfl
  | pos p => simpa [encodeNum, PosNum.natSize_to_nat] using encodePosNum_length p

/-- Mathlib's chosen natural-number string really is a binary-size encoding. -/
theorem encodeNat_length (n : ℕ) : (encodeNat n).length = Nat.size n := by
  simpa [encodeNat] using encodeNum_length (n : Num)

/-- The signed-to-natural bijection costs at most one extra bit. -/
theorem intCode_size_le (z : ℤ) : Nat.size (Equiv.intEquivNat z) ≤ z.natAbs.size + 1 := by
  have hz : Equiv.intEquivNat z ≤ 2 * z.natAbs := by
    cases z with
    | ofNat n => exact Nat.le_refl _
    | negSucc n =>
      change 2 * n + 1 ≤ 2 * (n + 1)
      omega
  apply Nat.size_le.mpr
  have habs := Nat.lt_size_self z.natAbs
  calc
    Equiv.intEquivNat z ≤ 2 * z.natAbs := hz
    _ < 2 * 2 ^ z.natAbs.size := Nat.mul_lt_mul_of_pos_left habs (by decide)
    _ = 2 ^ (z.natAbs.size + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Natural pairing doubles the maximum input bit length at most. -/
theorem pair_size_le (a b : ℕ) :
    (Nat.pair a b).size ≤ 2 * max a.size b.size := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ max a.size b.size :=
    Nat.size_le.mp (le_max_left _ _)
  have hb : b < 2 ^ max a.size b.size :=
    Nat.size_le.mp (le_max_right _ _)
  calc
    Nat.pair a b < (max a b + 1) ^ 2 := Nat.pair_lt_max_add_one_sq a b
    _ ≤ (2 ^ max a.size b.size) ^ 2 :=
      Nat.pow_le_pow_left (Nat.succ_le_of_lt (max_lt ha hb)) 2
    _ = 2 ^ (2 * max a.size b.size) := by rw [← pow_mul, Nat.mul_comm]

/-- Actual rational code length is linearly bounded in ordinary signed numerator
and positive denominator bit lengths. -/
theorem rationalEncoding_length_le (q : ℚ) :
    (rationalEncoding.encode q).length ≤
      2 * max (q.num.natAbs.size + 1) q.den.size := by
  change (encodeNat (rationalCode q)).length ≤ _
  rw [encodeNat_length]
  apply le_trans (pair_size_le _ _)
  exact Nat.mul_le_mul_left 2 (max_le_max (intCode_size_le _) (Nat.le_refl _))

/-- A fixed-dimensional coefficient vector has linear bit-framing overhead. -/
theorem vectorEncoding_length_le {n B : ℕ} (v : Fin n → ℚ)
    (h : ∀ i, max ((v i).num.natAbs.size + 1) (v i).den.size ≤ B) :
    ((vectorEncoding n).encode v).length ≤ n * (4 * B + 1) := by
  change (vectorEncode n v).length ≤ _
  rw [vectorEncode_length]
  calc
    (∑ i, (2 * (rationalEncoding.encode (v i)).length + 1)) ≤
        ∑ _i : Fin n, (4 * B + 1) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := le_trans (rationalEncoding_length_le (v i)) (Nat.mul_le_mul_left 2 (h i))
      omega
    _ = n * (4 * B + 1) := by simp

end Holant.Algebraic
