import Holant.Complexity.BinaryArithmetic.DivideBits
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Restoring binary square-root specification

A radix-four digit consists of two bits. Each digit uses shifts and one trial
binary subtraction, retaining a canonical square root and remainder. No natural
square-root operation occurs in the executable body. This is a list-level
specification, not yet a finite-machine running-time theorem.
-/

namespace Holant.Complexity.BinaryArithmetic.SquareRootBits

open Computability DivisionBits

abbrev Digit := Bool × Bool

/-- Append a radix-four input digit to the remainder. -/
def trialWord (d : Digit) (r : List Bool) : List Bool := shiftBit d.2 (shiftBit d.1 r)

/-- The difference between consecutive candidate squares is `4q+1`. -/
def threshold (q : List Bool) : List Bool := shiftBit true (shiftBit false q)

/-- One restoring square-root digit; comparison is the final bitwise borrow. -/
def step (d : Digit) (q r : List Bool) : List Bool × List Bool :=
  let w := trialWord d r
  let t := subBits false w (threshold q)
  if t.2 then (shiftBit false q, w)
  else (shiftBit true q, normalize t.1)

@[simp] theorem value_trialWord (d : Digit) (r : List Bool) :
    value (trialWord d r) = 4 * value r + 2 * d.1.toNat + d.2.toNat := by
  simp [trialWord, value_shiftBit]
  ring

@[simp] theorem value_threshold (q : List Bool) : value (threshold q) = 4 * value q + 1 := by
  simp [threshold, value_shiftBit]
  omega

/-- The root/remainder invariant is maintained with a single trial subtraction. -/
theorem step_spec (d : Digit) (q r : List Bool) (hq : Canonical q) (hr : Canonical r)
    (hlt : value r < 2 * value q + 1) :
    Canonical (step d q r).1 ∧ Canonical (step d q r).2 ∧
      value (step d q r).2 < 2 * value (step d q r).1 + 1 ∧
      value (step d q r).1 ^ 2 + value (step d q r).2 =
        4 * (value q ^ 2 + value r) + 2 * d.1.toNat + d.2.toNat := by
  have hhi : d.1.toNat ≤ 1 := by cases h : d.1 <;> decide
  have hlo : d.2.toNat ≤ 1 := by cases h : d.2 <;> decide
  have hb := subBits_borrow_iff false (trialWord d r) (threshold q)
  simp only [Bool.toNat_false, Nat.add_zero] at hb
  have hv := value_subBits false (trialWord d r) (threshold q)
  cases ht : (subBits false (trialWord d r) (threshold q)).2 with
  | false =>
    simp only [ht, Bool.false_eq_true, false_iff] at hb
    simp only [ht, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
    simp only [step, ht, Bool.false_eq_true, ↓reduceIte]
    refine ⟨canonical_shiftBit _ _ hq, canonical_normalize _, ?_, ?_⟩
    · simp only [value_normalize, value_shiftBit, Bool.toNat_true]
      rw [value_threshold, value_trialWord] at hv
      omega
    · simp only [value_normalize, value_shiftBit, Bool.toNat_true]
      rw [value_threshold, value_trialWord] at hv
      nlinarith
  | true =>
    simp only [ht, true_iff, value_threshold, value_trialWord] at hb
    simp only [step, ht, ↓reduceIte]
    refine ⟨canonical_shiftBit _ _ hq,
      canonical_shiftBit _ _ (canonical_shiftBit _ _ hr), ?_, ?_⟩
    · simp only [value_shiftBit, Bool.toNat_false, Nat.zero_add, value_trialWord]
      omega
    · simp only [value_shiftBit, Bool.toNat_false, Nat.zero_add, value_trialWord]
      ring

/-- Process input digits most-significant first. -/
def loop : List Digit → List Bool → List Bool → List Bool × List Bool
  | [], q, r => (q, r)
  | d :: ds, q, r => let next := step d q r; loop ds next.1 next.2

/-- Original little-endian bits grouped from the low end. An odd top digit is
padded by one high zero, never by a low zero that would change the value. -/
def groupBits : List Bool → List Digit
  | [] => []
  | lo :: [] => [(false, lo)]
  | lo :: hi :: rest => (hi, lo) :: groupBits rest

/-- Canonical root and remainder, using only the bitwise recurrence. -/
def sqrtBits (bits : List Bool) : List Bool × List Bool := loop (groupBits bits).reverse [] []

/-- Numeric interpretation of a little-endian radix-four digit stream. -/
def digitsValue : List Digit → ℕ
  | [] => 0
  | d :: ds => 2 * d.1.toNat + d.2.toNat + 4 * digitsValue ds

theorem digitsValue_append (a b : List Digit) :
    digitsValue (a ++ b) = digitsValue a + 4 ^ a.length * digitsValue b := by
  induction a with
  | nil => simp [digitsValue]
  | cons d ds ih =>
    simp only [List.cons_append, digitsValue, List.length_cons, ih, pow_succ]
    ring

theorem groupBits_value (bits : List Bool) : digitsValue (groupBits bits) = value bits := by
  induction bits using groupBits.induct with
  | case1 => rfl
  | case2 lo => simp [groupBits, digitsValue, value]
  | case3 lo hi rest ih =>
    simp only [groupBits, digitsValue, value, ih]
    ring

/-- Complete root/remainder correctness for any digit prefix and valid initial
root/remainder pair. All intermediate states remain canonical. -/
theorem loop_spec (ds : List Digit) (q r : List Bool) (hq : Canonical q) (hr : Canonical r)
    (hlt : value r < 2 * value q + 1) :
    Canonical (loop ds q r).1 ∧ Canonical (loop ds q r).2 ∧
      value (loop ds q r).2 < 2 * value (loop ds q r).1 + 1 ∧
      value (loop ds q r).1 ^ 2 + value (loop ds q r).2 =
        4 ^ ds.length * (value q ^ 2 + value r) + digitsValue ds.reverse := by
  induction ds generalizing q r with
  | nil => simp [loop, digitsValue, hq, hr, hlt]
  | cons d ds ih =>
    obtain ⟨hqn, hrn, hlt, he⟩ := step_spec d q r hq hr hlt
    have ht := ih (step d q r).1 (step d q r).2 hqn hrn hlt
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
    simp only [loop]
    rw [ht.2.2.2, he]
    simp only [List.length_cons, List.reverse_cons, digitsValue_append, List.length_reverse,
      digitsValue, Nat.mul_zero, Nat.add_zero, pow_succ]
    ring

/-- Exact square-root interval and remainder equation, with no canonical-input
restriction: high zero padding is harmless. -/
theorem sqrtBits_spec (bits : List Bool) :
    Canonical (sqrtBits bits).1 ∧ Canonical (sqrtBits bits).2 ∧
      value (sqrtBits bits).1 = Nat.sqrt (value bits) ∧
      value (sqrtBits bits).1 ^ 2 + value (sqrtBits bits).2 = value bits := by
  have ht := loop_spec (groupBits bits).reverse [] [] canonical_nil canonical_nil (by simp)
  simp only [List.reverse_reverse, value_nil, zero_pow (by decide : 2 ≠ 0),
    Nat.add_zero, Nat.mul_zero, Nat.zero_add, groupBits_value] at ht
  refine ⟨ht.1, ht.2.1, ?_, ht.2.2.2⟩
  apply Nat.eq_sqrt'.mpr
  have hl := ht.2.2.1
  have he := ht.2.2.2
  change value (sqrtBits bits).2 < 2 * value (sqrtBits bits).1 + 1 at hl
  change value (sqrtBits bits).1 ^ 2 + value (sqrtBits bits).2 = value bits at he
  constructor <;> nlinarith

/-- Canonical encoding of the literal natural square root and square remainder. -/
theorem sqrtBits_encodeNat (n : ℕ) :
    sqrtBits (encodeNat n) = (encodeNat (Nat.sqrt n), encodeNat (n - Nat.sqrt n ^ 2)) := by
  have ht := sqrtBits_spec (encodeNat n)
  simp only [value_encodeNat] at ht
  apply Prod.ext
  · exact canonical_injective _ _ ht.1 (canonical_encodeNat _) (by simpa using ht.2.2.1)
  · apply canonical_injective _ _ ht.2.1 (canonical_encodeNat _)
    simp only [value_encodeNat]
    rw [ht.2.2.1] at ht
    omega

/-- Exactly one new root bit is considered per radix-four digit. -/
theorem step_root_length_le (d : Digit) (q r : List Bool) :
    (step d q r).1.length ≤ q.length + 1 := by
  dsimp only [step]
  split <;> exact shiftBit_length_le _ _

theorem loop_root_length_le (ds : List Digit) (q r : List Bool) :
    (loop ds q r).1.length ≤ q.length + ds.length := by
  induction ds generalizing q r with
  | nil => simp [loop]
  | cons d ds ih =>
    have hs := step_root_length_le d q r
    have hi := ih (step d q r).1 (step d q r).2
    simp only [loop, List.length_cons]
    omega

/-- The executable grouping has at most half the input length, rounded up. -/
theorem groupBits_length (bits : List Bool) :
    2 * (groupBits bits).length ≤ bits.length + 1 := by
  induction bits using groupBits.induct with
  | case1 => simp [groupBits]
  | case2 lo => simp [groupBits]
  | case3 lo hi rest ih => simp only [groupBits, List.length_cons]; omega

/-- The remainder invariant gives a linear word-size bound at EVERY valid digit
boundary, independently of the final answer-size theorem. -/
theorem remainder_length_le (q r : List Bool) (_hq : Canonical q) (hr : Canonical r)
    (hlt : value r < 2 * value q + 1) : r.length ≤ q.length + 1 := by
  have hv : value r ≤ value (shiftBit false q) := by simp only [value_shiftBit]; omega
  exact (DivisionBits.canonical_length_le_of_value_le r (shiftBit false q)
    hr hv).trans (shiftBit_length_le false q)

/-- Both output words have linear size in the actual supplied binary input. -/
theorem sqrtBits_lengths (bits : List Bool) :
    2 * (sqrtBits bits).1.length ≤ bits.length + 1 ∧
      (sqrtBits bits).2.length ≤ (sqrtBits bits).1.length + 1 := by
  have hr := loop_root_length_le (groupBits bits).reverse [] []
  simp only [List.length_nil, Nat.zero_add, List.length_reverse] at hr
  have hg := groupBits_length bits
  have ht := loop_spec (groupBits bits).reverse [] [] canonical_nil canonical_nil (by simp)
  exact ⟨by change 2 * (loop (groupBits bits).reverse [] []).1.length ≤ _; omega,
    remainder_length_le _ _ ht.1 ht.2.1 ht.2.2.1⟩

end Holant.Complexity.BinaryArithmetic.SquareRootBits
