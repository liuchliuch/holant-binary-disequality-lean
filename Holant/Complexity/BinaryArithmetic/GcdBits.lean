import Holant.Complexity.BinaryArithmetic.DivideBits
import Mathlib.Data.Nat.GCD.Basic

/-!
# Bit-length-bounded Euclidean iteration

The recurrence invokes the existing binary long-division specification. No
natural division, remainder or gcd function occurs in its computational body.
Two nonterminal Euclidean steps more than halve the second operand, so linear
fuel in the input bit lengths suffices. The actual finite-machine realization
and transition-time analysis are separate from this semantic helper.
-/

namespace Holant.Complexity.BinaryArithmetic.GcdBits

open Computability

/-- Actual binary remainder computation, with the dividend read MSB first. -/
def remainder (a b : List Bool) : List Bool :=
  (DivisionBits.divideBits a.reverse b).2

/-- One nonterminal Euclidean update. -/
def next (a b : List Bool) : List Bool × List Bool := (b, remainder a b)

/-- Fuel bounds the number of Euclidean divisions, and is not a machine opcode. -/
def loop : ℕ → List Bool → List Bool → List Bool × List Bool
  | 0, a, b => (a, b)
  | fuel + 1, a, b => if b = [] then (a, []) else loop fuel b (remainder a b)

/-- Number of nonterminal Euclidean updates actually selected by the recurrence. -/
def count : ℕ → List Bool → List Bool → ℕ
  | 0, _, _ => 0
  | fuel + 1, a, b => if b = [] then 0 else 1 + count fuel b (remainder a b)

/-- A uniform linear bound in the two input bit lengths. -/
def fuel (a b : List Bool) : ℕ := 2 * (a.length + b.length) + 2

def gcdBits (a b : List Bool) : List Bool := (loop (fuel a b) a b).1

theorem canonical_remainder (a b : List Bool) (hb : Canonical b) : Canonical (remainder a b) :=
  (DivisionBits.canonical_divideBits a.reverse b hb).2

@[simp] theorem value_remainder (a b : List Bool) (hb : Canonical b) :
    value (remainder a b) = value a % value b := by
  simpa [remainder] using (DivisionBits.divideBits_values a.reverse b hb).2

@[simp] theorem remainder_encodeNat (a b : ℕ) :
    remainder (encodeNat a) (encodeNat b) = encodeNat (a % b) := by
  simp [remainder, DivisionBits.divideBits_encodeNat]

@[simp] theorem encodeNat_eq_nil (n : ℕ) : encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := congrArg value h
    simpa using hv
  · intro h
    subst n
    rfl

/-- Numeric notation in this theorem exposes the binary recurrence's specification. -/
theorem loop_encodeNat_succ (n a b : ℕ) :
    loop (n + 1) (encodeNat a) (encodeNat b) =
      if b = 0 then (encodeNat a, []) else loop n (encodeNat b) (encodeNat (a % b)) := by
  simp only [loop, encodeNat_eq_nil, remainder_encodeNat]

theorem count_encodeNat_succ (n a b : ℕ) :
    count (n + 1) (encodeNat a) (encodeNat b) =
      if b = 0 then 0 else 1 + count n (encodeNat b) (encodeNat (a % b)) := by
  simp only [count, encodeNat_eq_nil, remainder_encodeNat]

theorem remainder_length_le (a b : List Bool) (hb : Canonical b) :
    (remainder a b).length ≤ a.length := by
  simpa [remainder] using DivisionBits.divideBits_remainder_length_le a.reverse b hb

theorem canonical_loop (n : ℕ) (a b : List Bool) (ha : Canonical a) (hb : Canonical b) :
    Canonical (loop n a b).1 ∧ Canonical (loop n a b).2 := by
  induction n generalizing a b with
  | zero => exact ⟨ha, hb⟩
  | succ n ih =>
    by_cases hz : b = []
    · simp [loop, hz, ha]
    · simpa only [loop, hz, ↓reduceIte] using ih b (remainder a b) hb (canonical_remainder a b hb)

theorem count_le (n : ℕ) (a b : List Bool) : count n a b ≤ n := by
  induction n generalizing a b with
  | zero => simp [count]
  | succ n ih =>
    by_cases hz : b = []
    · simp [count, hz]
    · have h := ih b (remainder a b)
      simp only [count, hz, ↓reduceIte]
      omega

@[simp] theorem loop_zero_right (n : ℕ) (a : List Bool) : loop n a [] = (a, []) := by
  cases n <;> simp [loop]

/-- Fuel spent after the terminal pair performs no additional Euclidean updates. -/
theorem loop_count (n : ℕ) (a b : List Bool) : loop (count n a b) a b = loop n a b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    by_cases hz : b = []
    · simp [count, loop, hz]
    · simp only [count, hz, ↓reduceIte]
      rw [Nat.add_comm 1, loop, ite_eq_right hz, loop, ite_eq_right hz]
      exact ih b (remainder a b)

/-- A second Euclidean remainder is strictly smaller than half the original
positive divisor. This handles both sides of the half-size comparison explicitly. -/
theorem two_mul_mod_lt (b r : ℕ) (hr : 0 < r) (hrb : r < b) : 2 * (b % r) < b := by
  have hm := Nat.mod_lt b hr
  by_cases hhalf : 2 * r ≤ b
  · omega
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_lt hrb), Nat.mod_eq_of_lt (by omega : b - r < r)]
    omega

/-- Two iterations consume at least one binary place of the second operand.
The exponent is a size witness only; it is never processed by the machine. -/
theorem loop_terminates_of_lt_pow (k : ℕ) (a b : List Bool)
    (ha : Canonical a) (hb : Canonical b) (hsize : value b < 2 ^ k) :
    (loop (2 * k) a b).2 = [] := by
  induction k generalizing a b with
  | zero =>
    have hv : value b = value ([] : List Bool) := by simp only [pow_zero, value_nil] at *; omega
    have he := canonical_injective b [] hb canonical_nil hv
    simp [he]
  | succ k ih =>
    have htime : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [htime]
    by_cases hb0 : b = []
    · simp [hb0]
    · have hr := canonical_remainder a b hb
      by_cases hr0 : remainder a b = []
      · simp [loop, hb0, hr0]
      · have hbpos := value_pos_of_canonical hb hb0
        have hrpos := value_pos_of_canonical hr hr0
        have hrlt : value (remainder a b) < value b := by
          rw [value_remainder a b hb]
          exact Nat.mod_lt _ hbpos
        have hs := canonical_remainder b (remainder a b) hr
        have hhalve : 2 * value (remainder b (remainder a b)) < value b := by
          rw [value_remainder b (remainder a b) hr]
          exact two_mul_mod_lt _ _ hrpos hrlt
        have hnext : value (remainder b (remainder a b)) < 2 ^ k := by
          rw [pow_succ] at hsize
          omega
        have h := ih (remainder a b) (remainder b (remainder a b)) hr hs hnext
        simpa only [loop, hb0, hr0, ↓reduceIte] using h

/-- The promised input-bit-length fuel always reaches a zero second operand. -/
theorem loop_fuel_second (a b : List Bool) (ha : Canonical a) (hb : Canonical b) :
    (loop (fuel a b) a b).2 = [] := by
  have hp : 2 ^ b.length ≤ 2 ^ (a.length + b.length + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have ht := loop_terminates_of_lt_pow (a.length + b.length + 1) a b ha hb
    (lt_of_lt_of_le (value_lt_pow_length b) hp)
  simpa only [fuel, Nat.mul_add, Nat.mul_one] using ht

/-- The standard gcd invariant is preserved by the genuinely binary remainder step. -/
theorem gcd_next (a b : List Bool) (hb : Canonical b) :
    Nat.gcd (value b) (value (remainder a b)) = Nat.gcd (value a) (value b) := by
  rw [value_remainder a b hb]
  calc
    Nat.gcd (value b) (value a % value b) = Nat.gcd (value a % value b) (value b) := Nat.gcd_comm _ _
    _ = Nat.gcd (value b) (value a) := (Nat.gcd_rec _ _).symm
    _ = Nat.gcd (value a) (value b) := Nat.gcd_comm _ _

theorem gcd_loop (n : ℕ) (a b : List Bool) (ha : Canonical a) (hb : Canonical b) :
    Nat.gcd (value (loop n a b).1) (value (loop n a b).2) = Nat.gcd (value a) (value b) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    by_cases hz : b = []
    · simp [loop, hz]
    · simpa only [loop, hz, ↓reduceIte] using
        (ih b (remainder a b) hb (canonical_remainder a b hb)).trans (gcd_next a b hb)

/-- Intermediate numerical operands never exceed the larger original input. -/
theorem loop_value_max_le (n : ℕ) (a b : List Bool) (ha : Canonical a) (hb : Canonical b) :
    max (value (loop n a b).1) (value (loop n a b).2) ≤ max (value a) (value b) := by
  induction n generalizing a b with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    by_cases hz : b = []
    · simp [loop, hz]
    · have hi := ih b (remainder a b) hb (canonical_remainder a b hb)
      have hv : value (remainder a b) ≤ value a := by
        rw [value_remainder a b hb]
        exact Nat.mod_le _ _
      simp only [loop, hz, ↓reduceIte]
      omega

/-- The larger operand bit length never increases along any fuel prefix. -/
theorem loop_length_max_le (n : ℕ) (a b : List Bool) (ha : Canonical a) (hb : Canonical b) :
    max (loop n a b).1.length (loop n a b).2.length ≤ max a.length b.length := by
  induction n generalizing a b with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    by_cases hz : b = []
    · simp [loop, hz]
    · have hi := ih b (remainder a b) hb (canonical_remainder a b hb)
      have hl := remainder_length_le a b hb
      simp only [loop, hz, ↓reduceIte]
      omega

/-- Total live operand bit length likewise never exceeds the original total. -/
theorem loop_length_sum_le (n : ℕ) (a b : List Bool) (ha : Canonical a) (hb : Canonical b) :
    (loop n a b).1.length + (loop n a b).2.length ≤ a.length + b.length := by
  induction n generalizing a b with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    by_cases hz : b = []
    · simp [loop, hz]
    · have hi := ih b (remainder a b) hb (canonical_remainder a b hb)
      have hl := remainder_length_le a b hb
      simp only [loop, hz, ↓reduceIte]
      omega

/-- The terminal pair is the canonical gcd word and an empty zero word. -/
theorem loop_fuel (a b : List Bool) (ha : Canonical a) (hb : Canonical b) :
    loop (fuel a b) a b = (encodeNat (Nat.gcd (value a) (value b)), []) := by
  have hzero := loop_fuel_second a b ha hb
  have hgcd := gcd_loop (fuel a b) a b ha hb
  rw [hzero, value_nil, Nat.gcd_zero_right] at hgcd
  apply Prod.ext
  · exact canonical_injective _ _ (canonical_loop _ a b ha hb).1 (canonical_encodeNat _) (by simpa using hgcd)
  · exact hzero

/-- Exact compatibility with canonical natural-number inputs and output. -/
theorem loop_fuel_encodeNat (a b : ℕ) :
    loop (fuel (encodeNat a) (encodeNat b)) (encodeNat a) (encodeNat b) =
      (encodeNat (Nat.gcd a b), []) := by
  simpa using loop_fuel (encodeNat a) (encodeNat b) (canonical_encodeNat a) (canonical_encodeNat b)

theorem gcdBits_encodeNat (a b : ℕ) : gcdBits (encodeNat a) (encodeNat b) = encodeNat (Nat.gcd a b) := by
  simp [gcdBits, loop_fuel_encodeNat]

/-- The exact selected number of divisions is linear in the input bit lengths. -/
theorem count_fuel_le (a b : List Bool) :
    count (fuel a b) a b ≤ 2 * (a.length + b.length) + 2 := count_le _ _ _

end Holant.Complexity.BinaryArithmetic.GcdBits
