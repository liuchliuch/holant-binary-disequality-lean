import Holant.Complexity.BinaryArithmetic.Doubling
import Mathlib.Tactic.Ring

/-!
# Binary multiplication's shift/add specification

This file gives the word-level invariant and size bounds for the separately
compiled finite machine. The displayed cost recurrence is justified against
actual transitions in `Multiplication`, rather than installed as an instruction.
-/

namespace Holant.Complexity.BinaryArithmetic.MultiplyBits

open Computability

/-- One MSB-first Horner column, preserving the canonical zero encoding. -/
def next (bit : Bool) (multiplicand accumulator : List Bool) : List Bool :=
  if bit then addBits false (Doubling.shift accumulator) multiplicand
  else Doubling.shift accumulator

/-- The mathematical specification of the finite machine's repeated columns. -/
def run (multiplicand : List Bool) : List Bool → List Bool → List Bool
  | [], accumulator => accumulator
  | bit :: rest, accumulator => run multiplicand rest (next bit multiplicand accumulator)

theorem shift_length_le (word : List Bool) : (Doubling.shift word).length ≤ word.length + 1 := by
  cases word <;> simp [Doubling.shift]

theorem next_length_le (bit : Bool) (m a : List Bool) :
    (next bit m a).length ≤ a.length + m.length + 2 := by
  have hs := shift_length_le a
  have ha := addBits_length_le false (Doubling.shift a) m
  cases bit <;> simp only [next, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem value_next (bit : Bool) (m a : List Bool) :
    value (next bit m a) = 2 * value a + bit.toNat * value m := by
  cases bit <;> simp [next, value_addBits]

theorem canonical_next (bit : Bool) (m a : List Bool) (hm : Canonical m) (ha : Canonical a) :
    Canonical (next bit m a) := by
  cases bit
  · exact Doubling.canonical_shift a ha
  · exact canonical_addBits false _ _ (Doubling.canonical_shift a ha) hm

theorem canonical_run (m digits a : List Bool) (hm : Canonical m) (ha : Canonical a) :
    Canonical (run m digits a) := by
  induction digits generalizing a with
  | nil => exact ha
  | cons bit rest ih => exact ih _ (canonical_next bit m a hm ha)

theorem value_append (a b : List Bool) :
    value (a ++ b) = value a + 2 ^ a.length * value b := by
  induction a with
  | nil => simp
  | cons bit rest ih =>
    simp only [List.cons_append, value_cons, ih, List.length_cons, pow_succ]
    ring

/-- Horner's invariant includes an arbitrary already accumulated prefix. -/
theorem value_run (m digits a : List Bool) :
    value (run m digits a) = 2 ^ digits.length * value a + value digits.reverse * value m := by
  induction digits generalizing a with
  | nil => simp [run]
  | cons bit rest ih =>
    simp only [run, ih, value_next, List.length_cons, List.reverse_cons, value_append,
      List.length_reverse, value_cons, value_nil, Nat.mul_zero, Nat.add_zero, pow_succ]
    ring

theorem run_encodeNat (a b : ℕ) :
    run (encodeNat a) (encodeNat b).reverse [] = encodeNat (a * b) := by
  apply canonical_injective
  · exact canonical_run _ _ _ (canonical_encodeNat a) canonical_nil
  · exact canonical_encodeNat _
  · simp [value_run, Nat.mul_comm]

/-- Actual macro lengths: copy, compiled addition, and two result transfers.
`Multiplication.column_exact` proves this count operationally. -/
def columnTime (bit : Bool) (m a : List Bool) : ℕ :=
  if bit then
    1 + 2 * (m.length + 1) +
      (max (Doubling.shift a).length m.length + (next true m a).length + 2) +
      2 * ((next true m a).length + 1)
  else 1

/-- The terminal case includes clearing the preserved multiplicand and halting. -/
def time (m : List Bool) : List Bool → List Bool → ℕ
  | [], _ => m.length + 2
  | bit :: rest, a => columnTime bit m a + time m rest (next bit m a)

theorem columnTime_le (bit : Bool) (m a : List Bool) :
    columnTime bit m a ≤ 6 * (a.length + m.length + 3) := by
  have hs := shift_length_le a
  have hn := next_length_le true m a
  cases bit <;> simp only [columnTime, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A deliberately loose cubic bound, requiring no amortized-cost assumption. -/
theorem time_le (m digits a : List Bool) :
    time m digits a ≤
      (digits.length + 1) * (6 * (a.length + (digits.length + 1) * (m.length + 2) + 3)) := by
  induction digits generalizing a with
  | nil => simp only [time, List.length_nil]; omega
  | cons bit rest ih =>
    let bound := 6 * (a.length + (rest.length + 2) * (m.length + 2) + 3)
    have hnext := next_length_le bit m a
    have hcolumn : columnTime bit m a ≤ bound := by
      apply le_trans (columnTime_le bit m a)
      dsimp [bound]
      simp only [Nat.add_mul, Nat.mul_add]
      omega
    have htail : time m rest (next bit m a) ≤ (rest.length + 1) * bound := by
      apply le_trans (ih (next bit m a))
      apply Nat.mul_le_mul_left
      dsimp [bound]
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul]
      omega
    simp only [time, List.length_cons]
    calc
      columnTime bit m a + time m rest (next bit m a) ≤
          bound + (rest.length + 1) * bound := Nat.add_le_add hcolumn htail
      _ = (rest.length + 1 + 1) * bound := by ring

end Holant.Complexity.BinaryArithmetic.MultiplyBits
