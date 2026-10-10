import Holant.Complexity.Encoding

/-!
# Canonical binary words and the carry-adder specification

Words are least-significant-bit first, exactly as in `Computability.encodeNat`.
The ordinary positional value below is deliberately distinguished from mathlib's
`decodeNat`, whose behavior on noncanonical words is different. The algorithm in
this file is a specification; its implementation by finite TM2 instructions and
its transition counts are proved in `Addition`.
-/

namespace Holant.Complexity.BinaryArithmetic

open Computability

/-- Ordinary unsigned positional value, allowing high zero padding. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

/-- No high zero padding; zero is the empty word. -/
def Canonical : List Bool → Prop
  | [] => True
  | b :: bs => Canonical bs ∧ (bs = [] → b = true)

/-- One-column binary sum and carry, computed solely from three bits. -/
def digitSum (carry a b : Bool) : Bool := xor (xor carry a) b

def digitCarry (carry a b : Bool) : Bool := (carry && a) || (carry && b) || (a && b)

/-- Standard little-endian carry addition, padding the shorter operand with zeros. -/
def addBits (carry : Bool) : List Bool → List Bool → List Bool
  | [], [] => if carry then [true] else []
  | a :: as, [] => digitSum carry a false :: addBits (digitCarry carry a false) as []
  | [], b :: bs => digitSum carry false b :: addBits (digitCarry carry false b) [] bs
  | a :: as, b :: bs => digitSum carry a b :: addBits (digitCarry carry a b) as bs

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_cons (b : Bool) (bs : List Bool) :
    value (b :: bs) = b.toNat + 2 * value bs := rfl

@[simp] theorem canonical_nil : Canonical [] := trivial

@[simp] theorem digit_equation (carry a b : Bool) :
    (digitSum carry a b).toNat + 2 * (digitCarry carry a b).toNat =
      carry.toNat + a.toNat + b.toNat := by
  cases carry <;> cases a <;> cases b <;> decide

/-- Arithmetic correctness for every word, including padded noncanonical inputs. -/
theorem value_addBits (carry : Bool) (a b : List Bool) :
    value (addBits carry a b) = value a + value b + carry.toNat := by
  induction a generalizing b carry with
  | nil =>
    induction b generalizing carry with
    | nil => cases carry <;> simp [addBits, value]
    | cons bit bs ih =>
      simp only [addBits, value_cons, ih, value_nil]
      have h := digit_equation carry false bit
      simp only [Bool.toNat_false] at h
      omega
  | cons bit as ih =>
    cases b with
    | nil =>
      simp only [addBits, value_cons, ih, value_nil]
      have h := digit_equation carry bit false
      simp only [Bool.toNat_false] at h
      omega
    | cons bit' bs =>
      simp only [addBits, value_cons, ih]
      have h := digit_equation carry bit bit'
      omega

/-- Carry propagation adds at most one bit to the longer operand. -/
theorem addBits_length_le (carry : Bool) (a b : List Bool) :
    (addBits carry a b).length ≤ max a.length b.length + 1 := by
  induction a generalizing b carry with
  | nil =>
    induction b generalizing carry with
    | nil => cases carry <;> simp [addBits]
    | cons bit bs ih =>
      simpa [addBits] using Nat.succ_le_succ (ih (digitCarry carry false bit))
  | cons bit as ih =>
    cases b with
    | nil => simpa [addBits] using Nat.succ_le_succ (ih (digitCarry carry bit false) [])
    | cons bit' bs =>
      simpa [addBits, Nat.succ_max_succ] using
        Nat.succ_le_succ (ih (digitCarry carry bit bit') bs)

/-- Every canonical nonempty word has strictly positive positional value. -/
theorem value_pos_of_canonical {bs : List Bool} (h : Canonical bs) (hne : bs ≠ []) :
    0 < value bs := by
  induction bs with
  | nil => contradiction
  | cons b bs ih =>
    rcases h with ⟨ht, hb⟩
    cases bs with
    | nil => simp [hb rfl, value]
    | cons b' bs =>
      have hp := ih ht (List.cons_ne_nil _ _)
      simp only [value_cons] at hp ⊢
      omega

/-- The result retains the canonical high-bit convention. -/
theorem canonical_addBits (carry : Bool) (a b : List Bool)
    (ha : Canonical a) (hb : Canonical b) : Canonical (addBits carry a b) := by
  induction a generalizing b carry with
  | nil =>
    induction b generalizing carry with
    | nil => cases carry <;> simp [addBits, Canonical]
    | cons bit bs ih =>
      simp only [addBits, Canonical]
      refine ⟨ih _ hb.1, ?_⟩
      intro he
      have hv := value_addBits carry [] (bit :: bs)
      have hp := value_pos_of_canonical hb (List.cons_ne_nil _ _)
      simp only [addBits, he, value_cons, value_nil] at hv
      simp only [value_cons] at hp
      cases hs : digitSum carry false bit <;> simp [hs] at hv ⊢
      omega
  | cons bit as ih =>
    cases b with
    | nil =>
      simp only [addBits, Canonical]
      refine ⟨ih _ [] ha.1 trivial, ?_⟩
      intro he
      have hv := value_addBits carry (bit :: as) []
      have hp := value_pos_of_canonical ha (List.cons_ne_nil _ _)
      simp only [addBits, he, value_cons, value_nil] at hv
      simp only [value_cons] at hp
      cases hs : digitSum carry bit false <;> simp [hs] at hv ⊢
      omega
    | cons bit' bs =>
      simp only [addBits, Canonical]
      refine ⟨ih _ bs ha.1 hb.1, ?_⟩
      intro he
      have hv := value_addBits carry (bit :: as) (bit' :: bs)
      have hp := value_pos_of_canonical ha (List.cons_ne_nil _ _)
      simp only [addBits, he, value_cons, value_nil] at hv
      simp only [value_cons] at hp
      cases hs : digitSum carry bit bit' <;> simp [hs] at hv ⊢
      omega

/-- Canonical binary words are determined by their ordinary value. -/
theorem canonical_injective (a b : List Bool) (ha : Canonical a) (hb : Canonical b)
    (h : value a = value b) : a = b := by
  induction a generalizing b with
  | nil =>
    by_cases he : b = []
    · exact he.symm
    · have := value_pos_of_canonical hb he; simp at h; omega
  | cons bit as ih =>
    cases b with
    | nil =>
      have hp := value_pos_of_canonical ha (List.cons_ne_nil _ _)
      rw [h] at hp
      exact False.elim (Nat.not_lt_zero _ hp)
    | cons bit' bs =>
      simp only [value_cons] at h
      have hbit : bit = bit' := by
        cases bit <;> cases bit' <;> simp_all <;> omega
      subst bit'
      have ht : value as = value bs := by omega
      exact congrArg (List.cons bit) (ih bs ha.1 hb.1 ht)

@[simp] theorem canonical_encodePosNum (n : PosNum) : Canonical (encodePosNum n) := by
  induction n with
  | one => simp [encodePosNum, Canonical]
  | bit0 n ih => exact ⟨ih, fun h => False.elim (encodePosNum_nonempty n h)⟩
  | bit1 n ih => exact ⟨ih, fun h => False.elim (encodePosNum_nonempty n h)⟩

@[simp] theorem value_encodePosNum (n : PosNum) : value (encodePosNum n) = (n : ℕ) := by
  induction n with
  | one => rfl
  | bit0 n ih => simp [encodePosNum, ih, Nat.two_mul]
  | bit1 n ih => simp [encodePosNum, ih, Nat.two_mul]; omega

@[simp] theorem canonical_encodeNat (n : ℕ) : Canonical (encodeNat n) := by
  unfold encodeNat
  generalize (n : Num) = m
  cases m <;> simp [encodeNum]

@[simp] theorem value_encodeNat (n : ℕ) : value (encodeNat n) = n := by
  have h : ∀ m : Num, value (encodeNum m) = (m : ℕ) := by
    intro m; cases m <;> simp [encodeNum]
  simpa [encodeNat] using h (n : Num)

/-- Exact compatibility with the project's canonical natural-number codec. -/
theorem addBits_encodeNat (a b : ℕ) :
    addBits false (encodeNat a) (encodeNat b) = encodeNat (a + b) := by
  apply canonical_injective
  · exact canonical_addBits _ _ _ (canonical_encodeNat a) (canonical_encodeNat b)
  · exact canonical_encodeNat _
  · simp [value_addBits]

end Holant.Complexity.BinaryArithmetic
