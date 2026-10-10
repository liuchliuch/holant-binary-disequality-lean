import Holant.Proofs.CountingMachines.AnswerDecoder.Port.Holant.Complexity.BinaryArithmetic.SubtractBits
import Mathlib.Tactic.Ring


namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
open _root_.Holant.Complexity
open _root_.Holant.Complexity.BinaryArithmetic


/-!
# Binary long-division specification

The dividend is read most-significant-bit first. Each step shifts one bit into
the remainder and performs one binary trial subtraction. A borrow restores the
shifted remainder; otherwise the normalized difference is retained. These list
algorithms are specifications; actual finite-machine implementations are separate.
-/

namespace Holant.Complexity.BinaryArithmetic.DivisionBits

open Computability

/-- Shift in one low bit, preserving the empty encoding of zero. -/
def shiftBit (bit : Bool) : List Bool → List Bool
  | [] => if bit then [true] else []
  | head :: tail => bit :: head :: tail

@[simp] theorem value_shiftBit (bit : Bool) (word : List Bool) :
    value (shiftBit bit word) = bit.toNat + 2 * value word := by
  cases word <;> cases bit <;> simp [shiftBit, value]

theorem canonical_shiftBit (bit : Bool) (word : List Bool) (h : Canonical word) :
    Canonical (shiftBit bit word) := by
  cases word with
  | nil => cases bit <;> simp [shiftBit, Canonical]
  | cons head tail => exact ⟨h, by simp⟩

theorem shiftBit_length_le (bit : Bool) (word : List Bool) :
    (shiftBit bit word).length ≤ word.length + 1 := by
  cases word <;> cases bit <;> simp [shiftBit]

/-- A single radix-two quotient/remainder update, using only binary subtraction. -/
def step (bit : Bool) (divisor quotient remainder : List Bool) : List Bool × List Bool :=
  let shifted := shiftBit bit remainder
  let trial := subBits false shifted divisor
  if trial.2 then (shiftBit false quotient, shifted)
  else (shiftBit true quotient, normalize trial.1)

/-- Process the remaining most-significant-bit-first dividend. -/
def loop (divisor : List Bool) : List Bool → List Bool → List Bool → List Bool × List Bool
  | [], quotient, remainder => (quotient, remainder)
  | bit :: bits, quotient, remainder =>
      let next := step bit divisor quotient remainder
      loop divisor bits next.1 next.2

/-- The divisor-zero branch agrees with the total natural division convention. -/
def divideBits (bits divisor : List Bool) : List Bool × List Bool :=
  if divisor = [] then ([], normalize bits.reverse) else loop divisor bits [] []

theorem step_quotient_length_le (bit : Bool) (d q r : List Bool) :
    (step bit d q r).1.length ≤ q.length + 1 := by
  dsimp only [step]
  split <;> exact shiftBit_length_le _ _

theorem step_remainder_length_le (bit : Bool) (d q r : List Bool) :
    (step bit d q r).2.length ≤ max r.length d.length + 1 := by
  have hs := shiftBit_length_le bit r
  have hn := normalize_length_le (subBits false (shiftBit bit r) d).1
  rw [subBits_length] at hn
  dsimp only [step]
  split <;> dsimp <;> omega

theorem loop_quotient_length_le (d bits q r : List Bool) :
    (loop d bits q r).1.length ≤ q.length + bits.length := by
  induction bits generalizing q r with
  | nil => simp [loop]
  | cons bit bits ih =>
    have h := ih (step bit d q r).1 (step bit d q r).2
    have hs := step_quotient_length_le bit d q r
    simp only [loop, List.length_cons] at *
    omega

theorem loop_remainder_length_le (d bits q r : List Bool) :
    (loop d bits q r).2.length ≤ max r.length d.length + bits.length := by
  induction bits generalizing q r with
  | nil => simp [loop]
  | cons bit bits ih =>
    have h := ih (step bit d q r).1 (step bit d q r).2
    have hs := step_remainder_length_le bit d q r
    simp only [loop, List.length_cons] at *
    omega

/-- The MSB-first positional value. -/
def msbValue : List Bool → ℕ
  | [] => 0
  | bit :: bits => bit.toNat * 2 ^ bits.length + msbValue bits

theorem value_append (a b : List Bool) :
    value (a ++ b) = value a + 2 ^ a.length * value b := by
  induction a with
  | nil => simp
  | cons bit bits ih => simp [value, ih, pow_succ]; ring

@[simp] theorem msbValue_eq (bits : List Bool) : msbValue bits = value bits.reverse := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [msbValue, List.reverse_cons, value_append, value, ih, Nat.mul_comm, Nat.add_comm]

/-- A remainder below the divisor stays below it after one trial subtraction. -/
theorem step_spec (bit : Bool) (d q r : List Bool)
    (hq : Canonical q) (hr : Canonical r) (hlt : value r < value d) :
    Canonical (step bit d q r).1 ∧ Canonical (step bit d q r).2 ∧
      value (step bit d q r).2 < value d ∧
      value (step bit d q r).1 * value d + value (step bit d q r).2 =
        2 * (value q * value d + value r) + bit.toNat := by
  have hs := canonical_shiftBit bit r hr
  have hbit : bit.toNat ≤ 1 := by cases bit <;> decide
  have h2 : value (shiftBit bit r) < 2 * value d := by
    rw [value_shiftBit]; omega
  have hb := subBits_borrow_iff false (shiftBit bit r) d
  simp only [Bool.toNat_false, Nat.add_zero] at hb
  have hv := value_subBits false (shiftBit bit r) d
  cases hborrow : (subBits false (shiftBit bit r) d).2 with
  | false =>
    simp only [hborrow, Bool.false_eq_true, false_iff] at hb
    simp only [hborrow, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
    simp only [step, hborrow, Bool.false_eq_true, ↓reduceIte]
    refine ⟨canonical_shiftBit _ _ hq, canonical_normalize _, ?_, ?_⟩
    · rw [value_normalize]; omega
    · simp only [value_shiftBit, Bool.toNat_true, value_normalize]
      rw [value_shiftBit] at hv
      calc
        (1 + 2 * value q) * value d + value (subBits false (shiftBit bit r) d).1 =
            2 * (value q * value d) +
              (value (subBits false (shiftBit bit r) d).1 + value d) := by ring
        _ = 2 * (value q * value d + value r) + bit.toNat := by rw [hv]; ring
  | true =>
    simp only [hborrow, true_iff] at hb
    simp only [step, hborrow, ↓reduceIte]
    refine ⟨canonical_shiftBit _ _ hq, hs, hb, ?_⟩
    simp only [value_shiftBit, Bool.toNat_false, Nat.zero_add]
    ring

/-- Long division preserves the usual quotient/remainder equation. -/
theorem loop_spec (d bits q r : List Bool)
    (hq : Canonical q) (hr : Canonical r) (hlt : value r < value d) :
    Canonical (loop d bits q r).1 ∧ Canonical (loop d bits q r).2 ∧
      value (loop d bits q r).2 < value d ∧
      value (loop d bits q r).1 * value d + value (loop d bits q r).2 =
        (value q * value d + value r) * 2 ^ bits.length + msbValue bits := by
  induction bits generalizing q r with
  | nil => simpa [loop, msbValue] using And.intro hq (And.intro hr hlt)
  | cons bit bits ih =>
    obtain ⟨hq', hr', hlt', heq⟩ := step_spec bit d q r hq hr hlt
    obtain ⟨hfq, hfr, hflt, hfeq⟩ := ih _ _ hq' hr' hlt'
    refine ⟨hfq, hfr, hflt, ?_⟩
    simp only [loop]
    rw [hfeq, heq]
    simp only [List.length_cons, msbValue, pow_succ]
    ring

/-- Trial subtraction is exactly the strict comparison needed by long division. -/
theorem step_borrow_iff (bit : Bool) (d r : List Bool) :
    (subBits false (shiftBit bit r) d).2 = true ↔ value (shiftBit bit r) < value d := by
  simpa only [Bool.toNat_false, Nat.add_zero] using subBits_borrow_iff false (shiftBit bit r) d

/-- The shifted remainder is less than twice the divisor. Consequently one
successful subtraction is sufficient; an unbounded subtraction loop is unnecessary. -/
theorem shifted_remainder_lt_two (bit : Bool) (d r : List Bool) (h : value r < value d) :
    value (shiftBit bit r) < 2 * value d := by
  have hb : bit.toNat ≤ 1 := by cases bit <;> decide
  rw [value_shiftBit]
  omega

/-- Resolve the invariant into the unique standard natural quotient and remainder.
`Nat.div` and `Nat.mod` appear only in this specification theorem. -/
theorem loop_values (d bits q r : List Bool)
    (hq : Canonical q) (hr : Canonical r) (hlt : value r < value d) :
    value (loop d bits q r).1 =
        ((value q * value d + value r) * 2 ^ bits.length + msbValue bits) / value d ∧
      value (loop d bits q r).2 =
        ((value q * value d + value r) * 2 ^ bits.length + msbValue bits) % value d := by
  obtain ⟨_, _, hrem, heq⟩ := loop_spec d bits q r hq hr hlt
  have hdiv : ((value q * value d + value r) * 2 ^ bits.length + msbValue bits) / value d =
      value (loop d bits q r).1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · simp only [Nat.add_mul, Nat.one_mul] at heq ⊢
      omega
  refine ⟨hdiv.symm, ?_⟩
  have hmod := Nat.div_add_mod
    ((value q * value d + value r) * 2 ^ bits.length + msbValue bits) (value d)
  rw [hdiv, Nat.mul_comm (value d)] at hmod
  omega

/-- Both result words are canonical, including the total divisor-zero branch. -/
theorem canonical_divideBits (bits d : List Bool) (hd : Canonical d) :
    Canonical (divideBits bits d).1 ∧ Canonical (divideBits bits d).2 := by
  by_cases hz : d = []
  · simp [divideBits, hz, canonical_normalize]
  · have hp := value_pos_of_canonical hd hz
    obtain ⟨hq, hr, _, _⟩ := loop_spec d bits [] [] canonical_nil canonical_nil hp
    simpa only [divideBits, hz, ↓reduceIte] using And.intro hq hr

/-- Exact numerical correctness for every dividend word and canonical divisor.
Zero uses the conventional quotient zero and unchanged dividend remainder. -/
theorem divideBits_values (bits d : List Bool) (hd : Canonical d) :
    value (divideBits bits d).1 = value bits.reverse / value d ∧
      value (divideBits bits d).2 = value bits.reverse % value d := by
  by_cases hz : d = []
  · simp [divideBits, hz]
  · have hp := value_pos_of_canonical hd hz
    have h := loop_values d bits [] [] canonical_nil canonical_nil hp
    simpa [divideBits, hz] using h

/-- The canonical binary input and output words agree literally with the project codec. -/
theorem divideBits_encodeNat (a b : ℕ) :
    divideBits (encodeNat a).reverse (encodeNat b) = (encodeNat (a / b), encodeNat (a % b)) := by
  have hc := canonical_divideBits (encodeNat a).reverse (encodeNat b) (canonical_encodeNat b)
  have hv := divideBits_values (encodeNat a).reverse (encodeNat b) (canonical_encodeNat b)
  simp only [List.reverse_reverse, value_encodeNat] at hv
  apply Prod.ext
  · exact canonical_injective _ _ hc.1 (canonical_encodeNat _) (by simpa using hv.1)
  · exact canonical_injective _ _ hc.2 (canonical_encodeNat _) (by simpa using hv.2)

@[simp] theorem divideBits_zero_divisor (bits : List Bool) :
    divideBits bits [] = ([], normalize bits.reverse) := by simp [divideBits]

/-- A nonempty canonical word has a high one at its top binary place. -/
theorem pow_length_sub_one_le_value (word : List Bool) (hc : Canonical word) (hn : word ≠ []) :
    2 ^ (word.length - 1) ≤ value word := by
  induction word with
  | nil => contradiction
  | cons bit rest ih =>
    cases rest with
    | nil =>
      have hb := hc.2 rfl
      subst bit
      simp [value]
    | cons bit' rest =>
      have hh := ih hc.1 (List.cons_ne_nil _ _)
      simp only [List.length_cons, Nat.add_sub_cancel, value_cons, pow_succ] at hh ⊢
      omega

/-- A canonical word representing no larger a value needs no more bits, even
when the comparison word contains high zero padding. -/
theorem canonical_length_le_of_value_le (a b : List Bool) (ha : Canonical a)
    (hv : value a ≤ value b) : a.length ≤ b.length := by
  by_cases hn : a = []
  · simp [hn]
  · have hlo := pow_length_sub_one_le_value a ha hn
    have hhi := value_lt_pow_length b
    by_contra hlen
    have he : b.length ≤ a.length - 1 := by omega
    have hp : 2 ^ b.length ≤ 2 ^ (a.length - 1) := Nat.pow_le_pow_right (by decide) he
    omega

/-- During a valid long-division run the remainder occupies at most divisor length. -/
theorem loop_remainder_length_le_divisor (d bits q r : List Bool)
    (hq : Canonical q) (hr : Canonical r) (hlt : value r < value d) :
    (loop d bits q r).2.length ≤ d.length := by
  obtain ⟨_, hc, hv, _⟩ := loop_spec d bits q r hq hr hlt
  exact canonical_length_le_of_value_le _ _ hc (Nat.le_of_lt hv)

/-- The quotient never exceeds the number of input bits, independent of divisor validity. -/
theorem divideBits_quotient_length_le (bits d : List Bool) :
    (divideBits bits d).1.length ≤ bits.length := by
  by_cases hz : d = []
  · simp [divideBits, hz]
  · simpa [divideBits, hz] using loop_quotient_length_le d bits [] []

/-- Even the divisor-zero remainder is no longer than the dividend input. -/
theorem divideBits_remainder_length_le (bits d : List Bool) (hd : Canonical d) :
    (divideBits bits d).2.length ≤ bits.length := by
  have hc := (canonical_divideBits bits d hd).2
  have hv := (divideBits_values bits d hd).2
  have hle : value (divideBits bits d).2 ≤ value bits.reverse := by
    rw [hv]
    exact Nat.mod_le _ _
  simpa only [List.length_reverse] using canonical_length_le_of_value_le _ _ hc hle

/-- For nonzero divisors the remainder also fits within the divisor word. -/
theorem divideBits_remainder_length_le_divisor (bits d : List Bool)
    (hd : Canonical d) (hn : d ≠ []) :
    (divideBits bits d).2.length ≤ d.length := by
  have hp := value_pos_of_canonical hd hn
  simpa [divideBits, hn] using
    loop_remainder_length_le_divisor d bits [] [] canonical_nil canonical_nil hp

/-- A trial remainder before subtraction requires at most one extra divisor bit. -/
theorem shifted_remainder_length_le (bit : Bool) (d r : List Bool)
    (hr : Canonical r) (hlt : value r < value d) :
    (shiftBit bit r).length ≤ d.length + 1 := by
  have hlen := canonical_length_le_of_value_le r d hr (Nat.le_of_lt hlt)
  exact le_trans (shiftBit_length_le bit r) (Nat.add_le_add_right hlen 1)

end Holant.Complexity.BinaryArithmetic.DivisionBits

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
