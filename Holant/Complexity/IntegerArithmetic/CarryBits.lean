import Holant.Complexity.IntegerArithmetic.Encoding
import Holant.Complexity.BinaryArithmetic.MultiplyBits

/-! Finite carry/borrow word specifications for parsing and reconstructing the
actual parity integer codec. Their concrete transition compilation is separate. -/

namespace Holant.Complexity.IntegerArithmetic

open Computability BinaryArithmetic

def increment : List Bool → List Bool
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => false :: increment rest

def carryCount : List Bool → ℕ
  | [] => 0
  | false :: _ => 0
  | true :: rest => carryCount rest + 1

def carryTail : List Bool → List Bool
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => carryTail rest

def decrement : List Bool → List Bool
  | [] => []
  | false :: rest => true :: decrement rest
  | true :: rest => Doubling.shift rest

def borrowCount : List Bool → ℕ
  | [] => 0
  | true :: _ => 0
  | false :: rest => borrowCount rest + 1

def borrowTail : List Bool → List Bool
  | [] => []
  | true :: rest => Doubling.shift rest
  | false :: rest => borrowTail rest

@[simp] theorem increment_nonempty (word : List Bool) : increment word ≠ [] := by
  cases word with
  | nil => simp [increment]
  | cons bit rest => cases bit <;> simp [increment]

@[simp] theorem value_increment (word : List Bool) : value (increment word) = value word + 1 := by
  induction word with
  | nil => simp [increment, value]
  | cons bit rest ih => cases bit <;> simp [increment, value, ih] <;> omega

theorem canonical_increment (word : List Bool) (h : Canonical word) : Canonical (increment word) := by
  induction word with
  | nil => simp [increment, Canonical]
  | cons bit rest ih =>
    cases bit
    · exact ⟨h.1, by simp⟩
    · exact ⟨ih h.1, fun he => False.elim (increment_nonempty rest he)⟩

theorem increment_encodeNat (n : ℕ) : increment (encodeNat n) = encodeNat (n + 1) := by
  apply canonical_injective
  · exact canonical_increment _ (canonical_encodeNat _)
  · exact canonical_encodeNat _
  · simp

theorem carryCount_le (word : List Bool) : carryCount word ≤ word.length := by
  induction word with
  | nil => simp [carryCount]
  | cons bit rest ih =>
    cases bit <;> simp [carryCount]
    omega

theorem increment_length_le (word : List Bool) : (increment word).length ≤ word.length + 1 := by
  induction word with
  | nil => simp [increment]
  | cons bit rest ih =>
    cases bit <;> simp [increment]
    omega

theorem increment_split (word : List Bool) :
    increment word = List.replicate (carryCount word) false ++ carryTail word := by
  induction word with
  | nil => simp [increment, carryCount, carryTail]
  | cons bit rest ih => cases bit <;> simp [increment, carryCount, carryTail, List.replicate_succ, ih]

theorem canonical_decrement (word : List Bool) (h : Canonical word) : Canonical (decrement word) := by
  induction word with
  | nil => trivial
  | cons bit rest ih =>
    cases bit
    · exact ⟨ih h.1, by simp⟩
    · exact Doubling.canonical_shift rest h.1

theorem value_decrement (word : List Bool) (h : Canonical word) :
    value (decrement word) = value word - 1 := by
  induction word with
  | nil => simp [decrement]
  | cons bit rest ih =>
    cases bit
    · have hn : rest ≠ [] := by intro he; have hb := h.2 he; contradiction
      have hp := value_pos_of_canonical h.1 hn
      simp only [decrement, value_cons, Bool.toNat_false, Bool.toNat_true, ih h.1]
      omega
    · simp only [decrement, Doubling.value_shift, value_cons, Bool.toNat_true]
      omega

theorem decrement_encodeNat (n : ℕ) : decrement (encodeNat n) = encodeNat (n - 1) := by
  apply canonical_injective
  · exact canonical_decrement _ (canonical_encodeNat _)
  · exact canonical_encodeNat _
  · simp [value_decrement _ (canonical_encodeNat _)]

theorem borrowCount_le (word : List Bool) : borrowCount word ≤ word.length := by
  induction word with
  | nil => simp [borrowCount]
  | cons bit rest ih =>
    cases bit <;> simp [borrowCount]
    omega

theorem decrement_length_le (word : List Bool) : (decrement word).length ≤ word.length := by
  induction word with
  | nil => simp [decrement]
  | cons bit rest ih =>
    cases bit
    · simpa [decrement] using Nat.succ_le_succ ih
    · simpa [decrement] using MultiplyBits.shift_length_le rest

theorem decrement_split (word : List Bool) :
    decrement word = List.replicate (borrowCount word) true ++ borrowTail word := by
  induction word with
  | nil => simp [decrement, borrowCount, borrowTail]
  | cons bit rest ih => cases bit <;> simp [decrement, borrowCount, borrowTail, List.replicate_succ, ih]

/-- Reconstruct the established parity code, explicitly ruling out negative zero. -/
def recode (sign : Bool) (magnitude : List Bool) : List Bool :=
  if magnitude = [] then [] else if sign then true :: decrement magnitude else false :: magnitude

theorem recode_encodeNat (sign : Bool) (n : ℕ) :
    recode sign (encodeNat n) = encoding.encode (ofSign sign n) := by
  cases sign with
  | false =>
    cases h : encodeNat n <;> simp [recode, ofSign, encoding_ofNat, Doubling.shift, h]
  | true =>
    cases n with
    | zero => rfl
    | succ n =>
      change recode true (encodeNat (n + 1)) = encoding.encode (Int.negSucc n)
      simp [recode, decrement_encodeNat]

def magnitudeBits (z : ℤ) : List Bool :=
  if negative z then increment (encoding.encode z).tail else (encoding.encode z).tail

@[simp] theorem magnitudeBits_eq (z : ℤ) : magnitudeBits z = encodeNat z.natAbs := by
  unfold magnitudeBits
  rw [encoding_tail]
  cases z <;> simp [negative, payload, increment_encodeNat]

theorem magnitudeBits_length_le (z : ℤ) : (encodeNat z.natAbs).length ≤ (encoding.encode z).length + 1 := by
  rw [← magnitudeBits_eq]
  have ht : (encoding.encode z).tail.length ≤ (encoding.encode z).length := by simp
  have hi := increment_length_le (encoding.encode z).tail
  unfold magnitudeBits
  split <;> omega

/-- A size bound inherited from the existing multiplication specification. -/
theorem multiply_run_length_le (m digits a : List Bool) :
    (MultiplyBits.run m digits a).length ≤ a.length + digits.length * (m.length + 2) := by
  induction digits generalizing a with
  | nil => simp [MultiplyBits.run]
  | cons bit rest ih =>
    have hn := MultiplyBits.next_length_le bit m a
    have hi := ih (MultiplyBits.next bit m a)
    simp only [MultiplyBits.run, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem product_length_le (a b : ℕ) :
    (encodeNat (a * b)).length ≤ (encodeNat b).length * ((encodeNat a).length + 2) := by
  have h := multiply_run_length_le (encodeNat a) (encodeNat b).reverse []
  simpa only [MultiplyBits.run_encodeNat, List.length_nil, Nat.zero_add, List.length_reverse] using h

end Holant.Complexity.IntegerArithmetic
