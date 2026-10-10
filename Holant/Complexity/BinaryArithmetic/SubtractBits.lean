import Holant.Complexity.BinaryArithmetic.Bits

/-!
# Binary borrow subtraction and normalization

Words are least-significant-bit first. The subtraction pass emits exactly the
maximum input length, retaining a final underflow bit; normalization trims high
zero padding. These are specifications for the finite-machine implementation.
-/

namespace Holant.Complexity.BinaryArithmetic

open Computability

/-- The result bit of a binary subtraction column. -/
def digitDiff (borrow a b : Bool) : Bool := xor (xor borrow a) b

/-- The outgoing borrow of a binary subtraction column. -/
def digitBorrow (borrow a b : Bool) : Bool :=
  (!a && b) || (!a && borrow) || (b && borrow)

/-- Little-endian subtraction, padding the shorter input by zero bits. -/
def subBits (borrow : Bool) : List Bool → List Bool → List Bool × Bool
  | [], [] => ([], borrow)
  | a :: as, [] =>
      let rest := subBits (digitBorrow borrow a false) as []
      (digitDiff borrow a false :: rest.1, rest.2)
  | [], b :: bs =>
      let rest := subBits (digitBorrow borrow false b) [] bs
      (digitDiff borrow false b :: rest.1, rest.2)
  | a :: as, b :: bs =>
      let rest := subBits (digitBorrow borrow a b) as bs
      (digitDiff borrow a b :: rest.1, rest.2)

/-- Remove high false bits by scanning the reversed word. -/
def normalize (bs : List Bool) : List Bool :=
  (bs.reverse.dropWhile (fun b => !b)).reverse

/-- Truncated natural subtraction: discard the result on final underflow. -/
def subNatBits (a b : List Bool) : List Bool :=
  if (subBits false a b).2 then [] else normalize (subBits false a b).1

theorem subtract_digit_equation (borrow a b : Bool) :
    (digitDiff borrow a b).toNat + b.toNat + borrow.toNat =
      a.toNat + 2 * (digitBorrow borrow a b).toNat := by
  cases borrow <;> cases a <;> cases b <;> decide

/-- The pass emits one bit for each padded input column. -/
theorem subBits_length (borrow : Bool) (a b : List Bool) :
    (subBits borrow a b).1.length = max a.length b.length := by
  induction a generalizing b borrow with
  | nil =>
    induction b generalizing borrow with
    | nil => simp [subBits]
    | cons bit bs ih => simpa [subBits] using congrArg Nat.succ (ih (digitBorrow borrow false bit))
  | cons bit as ih =>
    cases b with
    | nil => simpa [subBits] using congrArg Nat.succ (ih (digitBorrow borrow bit false) [])
    | cons bit' bs =>
      simpa [subBits, Nat.succ_max_succ] using
        congrArg Nat.succ (ih (digitBorrow borrow bit bit') bs)

/-- The borrow is the high bit needed to balance subtraction over natural values. -/
theorem value_subBits (borrow : Bool) (a b : List Bool) :
    value (subBits borrow a b).1 + value b + borrow.toNat =
      value a + 2 ^ (max a.length b.length) * (subBits borrow a b).2.toNat := by
  induction a generalizing b borrow with
  | nil =>
    induction b generalizing borrow with
    | nil => simp [subBits, value]
    | cons bit bs ih =>
      have hi := ih (digitBorrow borrow false bit)
      have hd := subtract_digit_equation borrow false bit
      cases hf : (subBits (digitBorrow borrow false bit) [] bs).2 <;>
        simp only [subBits, hf, pow_succ, value_nil, value_cons, List.length_nil,
          List.length_cons, Nat.zero_max, Bool.toNat_true, Bool.toNat_false,
          Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero] at hi hd ⊢ <;> omega
  | cons bit as ih =>
    cases b with
    | nil =>
      have hi := ih (digitBorrow borrow bit false) []
      have hd := subtract_digit_equation borrow bit false
      cases hf : (subBits (digitBorrow borrow bit false) as []).2 <;>
        simp [subBits, hf, pow_succ] at hi hd ⊢ <;> omega
    | cons bit' bs =>
      have hi := ih (digitBorrow borrow bit bit') bs
      have hd := subtract_digit_equation borrow bit bit'
      cases hf : (subBits (digitBorrow borrow bit bit') as bs).2 <;>
        simp [subBits, hf, Nat.succ_max_succ, pow_succ] at hi hd ⊢ <;> omega

/-- Positional value fits strictly below the word's binary place bound. -/
theorem value_lt_pow_length (bs : List Bool) : value bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp [value, pow_succ] at * <;> omega

/-- Final underflow is equivalent to strict inequality of the minuend and subtrahend. -/
theorem subBits_borrow_iff (borrow : Bool) (a b : List Bool) :
    (subBits borrow a b).2 = true ↔ value a < value b + borrow.toNat := by
  have hv := value_subBits borrow a b
  have hl := value_lt_pow_length (subBits borrow a b).1
  rw [subBits_length] at hl
  cases hf : (subBits borrow a b).2 <;> simp [hf] at hv ⊢ <;> omega

@[simp] theorem normalize_nil : normalize [] = [] := rfl

@[simp] theorem normalize_append_false (bs : List Bool) :
    normalize (bs ++ [false]) = normalize bs := by
  simp [normalize]

@[simp] theorem normalize_append_true (bs : List Bool) :
    normalize (bs ++ [true]) = bs ++ [true] := by
  simp [normalize]

@[simp] theorem normalize_reverse_cons_false (bs : List Bool) :
    normalize (false :: bs).reverse = normalize bs.reverse := by
  simp [normalize]

@[simp] theorem normalize_reverse_cons_true (bs : List Bool) :
    normalize (true :: bs).reverse = (true :: bs).reverse := by
  simp [normalize]

/-- An arbitrary low-bit prefix followed by a high one is canonical. -/
theorem canonical_append_true (bs : List Bool) : Canonical (bs ++ [true]) := by
  induction bs with
  | nil => simp [Canonical]
  | cons bit bs ih => simp [Canonical, ih]

@[simp] theorem value_append_false (bs : List Bool) : value (bs ++ [false]) = value bs := by
  induction bs with
  | nil => simp [value]
  | cons bit bs ih => simp [value, ih]

/-- Removing high zero padding preserves the represented number. -/
@[simp] theorem value_normalize (bs : List Bool) : value (normalize bs) = value bs := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs bit ih => cases bit <;> simp [ih]

/-- Every normalized word uses the project's canonical high-bit convention. -/
theorem canonical_normalize (bs : List Bool) : Canonical (normalize bs) := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs bit ih => cases bit <;> simp [ih, canonical_append_true]

/-- Normalization never increases the number of bits. -/
theorem normalize_length_le (bs : List Bool) : (normalize bs).length ≤ bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs bit ih =>
      cases bit
      · simp only [normalize_append_false, List.length_append, List.length_singleton]
        omega
      · simp

/-- Canonical words are already normalized. -/
theorem normalize_eq_self (bs : List Bool) (h : Canonical bs) : normalize bs = bs :=
  canonical_injective _ _ (canonical_normalize bs) h (value_normalize bs)

@[simp] theorem normalize_idempotent (bs : List Bool) :
    normalize (normalize bs) = normalize bs :=
  normalize_eq_self _ (canonical_normalize bs)

@[simp] theorem normalize_encodeNat (n : ℕ) : normalize (encodeNat n) = encodeNat n :=
  normalize_eq_self _ (canonical_encodeNat n)

/-- The canonical truncated result fits within the longer input word. -/
theorem subNatBits_length_le (a b : List Bool) :
    (subNatBits a b).length ≤ max a.length b.length := by
  unfold subNatBits
  split
  · simp
  · exact (normalize_length_le _).trans (Nat.le_of_eq (subBits_length false a b))

/-- Truncated subtraction always produces a canonical output word. -/
theorem canonical_subNatBits (a b : List Bool) : Canonical (subNatBits a b) := by
  unfold subNatBits
  split <;> simp [canonical_normalize]

/-- Truncated subtraction agrees with natural subtraction on positional values. -/
@[simp] theorem value_subNatBits (a b : List Bool) :
    value (subNatBits a b) = value a - value b := by
  have hv := value_subBits false a b
  have hb := subBits_borrow_iff false a b
  cases hf : (subBits false a b).2 <;> simp [hf, subNatBits] at hv hb ⊢ <;> omega

/-- Exact compatibility with the canonical natural-number codec. -/
theorem subNatBits_encodeNat (a b : ℕ) :
    subNatBits (encodeNat a) (encodeNat b) = encodeNat (a - b) := by
  apply canonical_injective
  · exact canonical_subNatBits _ _
  · exact canonical_encodeNat _
  · simp

end Holant.Complexity.BinaryArithmetic
