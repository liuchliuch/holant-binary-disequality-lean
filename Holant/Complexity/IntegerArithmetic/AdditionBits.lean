import Holant.Complexity.IntegerArithmetic.CarryBits
import Holant.Complexity.BinaryArithmetic.SubtractBits

/-! Signed addition directly on the established parity codes. Equal signs use
one carry addition. Opposite signs use the two borrow differences, retaining the
nonnegative one; a positive answer removes the offset by one actual decrement.
This is a word specification, not a machine instruction. -/

namespace Holant.Complexity.IntegerArithmetic

open Computability BinaryArithmetic

def mixedBits (negativeFirst : Bool) (a b : List Bool) : List Bool :=
  if (subBits false a b).2 then
    if negativeFirst then decrement (normalize (subBits false b a).1) else normalize (subBits false b a).1
  else
    if negativeFirst then normalize (subBits false a b).1 else decrement (normalize (subBits false a b).1)

def sumBits (sa sb : Bool) (a b : List Bool) : List Bool :=
  if sa = sb then addBits sa a b else mixedBits sa a b

theorem addBits_carry_encodeNat (c : Bool) (a b : ℕ) :
    addBits c (encodeNat a) (encodeNat b) = encodeNat (a + b + c.toNat) := by
  apply canonical_injective
  · exact canonical_addBits _ _ _ (canonical_encodeNat _) (canonical_encodeNat _)
  · exact canonical_encodeNat _
  · simp [value_addBits]

theorem normalize_subBits_of_no_borrow (a b : List Bool) (h : (subBits false a b).2 = false) :
    normalize (subBits false a b).1 = subNatBits a b := by simp [subNatBits, h]

theorem mixedBits_encodeNat (sign : Bool) (a b : ℕ) :
    mixedBits sign (encodeNat a) (encodeNat b) =
      if a < b then encodeNat (if sign then b - a - 1 else b - a)
      else encodeNat (if sign then a - b else a - b - 1) := by
  have hf : (subBits false (encodeNat a) (encodeNat b)).2 = true ↔ a < b := by
    simpa using subBits_borrow_iff false (encodeNat a) (encodeNat b)
  have hr : (subBits false (encodeNat b) (encodeNat a)).2 = true ↔ b < a := by
    simpa using subBits_borrow_iff false (encodeNat b) (encodeNat a)
  by_cases h : a < b
  · have hb := hf.mpr h
    have hbr : (subBits false (encodeNat b) (encodeNat a)).2 = false := by
      cases he : (subBits false (encodeNat b) (encodeNat a)).2
      · rfl
      · have := hr.mp he; omega
    simp only [mixedBits, hb, ↓reduceIte, h]
    rw [normalize_subBits_of_no_borrow _ _ hbr, subNatBits_encodeNat]
    cases sign <;> simp [decrement_encodeNat]
  · have hb : (subBits false (encodeNat a) (encodeNat b)).2 = false := by
      cases he : (subBits false (encodeNat a) (encodeNat b)).2
      · rfl
      · exact False.elim (h (hf.mp he))
    simp only [mixedBits, hb, Bool.false_eq_true, ↓reduceIte, h]
    rw [normalize_subBits_of_no_borrow _ _ hb, subNatBits_encodeNat]
    cases sign <;> simp [decrement_encodeNat]

theorem code_ofNat_add_negSucc (m n : ℕ) :
    Equiv.intEquivNat ((m : ℤ) + Int.negSucc n) =
      if 2 * m < 2 * n + 1 then (2 * n + 1) - 2 * m else 2 * m - (2 * n + 1) - 1 := by
  by_cases h : m ≤ n
  · have hz : (m : ℤ) + Int.negSucc n = Int.negSucc (n - m) := by
      simp only [Int.negSucc_eq]
      omega
    rw [hz, code_negSucc]
    split <;> omega
  · have hz : (m : ℤ) + Int.negSucc n = ((m - (n + 1) : ℕ) : ℤ) := by
      simp only [Int.negSucc_eq]
      omega
    rw [hz, code_ofNat]
    split <;> omega

/-- Literal correctness in the same signed codec, including cancellation to empty zero. -/
theorem sumBits_encoding (a b : ℤ) :
    sumBits (negative a) (negative b) (encoding.encode a) (encoding.encode b) = encoding.encode (a + b) := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      simp only [negative, sumBits, ↓reduceIte, encoding, addBits_carry_encodeNat, Bool.toNat_false,
        Nat.add_zero]
      congr 1
      change 2 * m + 2 * n = 2 * (m + n)
      omega
    | negSucc n =>
      change mixedBits false (encodeNat (2 * m)) (encodeNat (2 * n + 1)) =
        encodeNat (Equiv.intEquivNat ((m : ℤ) + Int.negSucc n))
      rw [mixedBits_encodeNat, code_ofNat_add_negSucc]
      split <;> rfl
  | negSucc m =>
    cases b with
    | ofNat n =>
      change mixedBits true (encodeNat (2 * m + 1)) (encodeNat (2 * n)) =
        encodeNat (Equiv.intEquivNat (Int.negSucc m + (n : ℤ)))
      rw [mixedBits_encodeNat, Int.add_comm, code_ofNat_add_negSucc]
      simp only [↓reduceIte]
      split <;> split <;> congr 1 <;> omega
    | negSucc n =>
      simp only [negative, sumBits, ↓reduceIte, encoding, code_negSucc, addBits_carry_encodeNat, Bool.toNat_true]
      have hz : Int.negSucc m + Int.negSucc n = Int.negSucc (m + n + 1) := by
        simp only [Int.negSucc_eq]
        omega
      rw [hz, code_negSucc]
      congr 1
      omega

end Holant.Complexity.IntegerArithmetic
