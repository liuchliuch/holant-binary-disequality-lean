import Holant.Complexity.BinaryArithmetic.EncodedAddition
import Holant.Complexity.BinaryArithmetic.Doubling
import Holant.Algebraic.RationalEncoding

/-!
# Faithful integer bits matching the established rational numerator convention

The scalar code is exactly `encodeNat (Equiv.intEquivNat z)`: nonnegative `n`
has natural code `2*n`, and negative successor `-(n+1)` has code `2*n+1`.
It is therefore the same integer convention used inside `rationalCode`; this
module does not replace the established rational pairing codec.
-/

namespace Holant.Complexity.IntegerArithmetic

open Computability BinaryArithmetic

/-- The parity sign bit of the established integer-to-natural equivalence. -/
def negative : ℤ → Bool
  | .ofNat _ => false
  | .negSucc _ => true

/-- Negative integers carry magnitude minus one in their parity-code tail. -/
def payload : ℤ → ℕ
  | .ofNat n => n
  | .negSucc n => n

def encoding : Encoding ℤ Bool where
  encode z := encodeNat (Equiv.intEquivNat z)
  decode bits := some (Equiv.intEquivNat.symm (decodeNat bits))
  decode_encode z := by simp

/-- Both integer words retain their entire bits in the previously used framing. -/
def pairEncoding : Encoding (ℤ × ℤ) Bool where
  encode p := Holant.Algebraic.frame (encoding.encode p.1).reverse ++ (encoding.encode p.2).reverse
  decode bits := (Holant.Algebraic.unframe bits).map fun p =>
    (Equiv.intEquivNat.symm (decodeNat p.1.reverse), Equiv.intEquivNat.symm (decodeNat p.2.reverse))
  decode_encode p := by simp [encoding]

@[simp] theorem code_ofNat (n : ℕ) : Equiv.intEquivNat (n : ℤ) = 2 * n := rfl
@[simp] theorem code_negSucc (n : ℕ) : Equiv.intEquivNat (.negSucc n) = 2 * n + 1 := rfl

/-- Odd codes have an actual leading one, including the code for minus one. -/
theorem encodeNat_odd (n : ℕ) : encodeNat (2 * n + 1) = true :: encodeNat n := by
  symm
  apply canonical_injective
  · exact ⟨canonical_encodeNat n, by simp⟩
  · exact canonical_encodeNat _
  · simp; omega

@[simp] theorem encodeNat_eq_nil (n : ℕ) : encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h; have hv := congrArg value h; simpa using hv
  · rintro rfl; rfl

@[simp] theorem encoding_negSucc (n : ℕ) : encoding.encode (.negSucc n) = true :: encodeNat n :=
  encodeNat_odd n

@[simp] theorem encoding_ofNat (n : ℕ) : encoding.encode (n : ℤ) = Doubling.shift (encodeNat n) := by
  simp only [encoding, code_ofNat, Doubling.shift_encodeNat]

/-- Reading the low parity bit is a finite sign operation, with empty zero positive. -/
theorem encoding_head (z : ℤ) : (encoding.encode z).head?.getD false = negative z := by
  cases z with
  | ofNat n => cases h : encodeNat n <;> simp [encoding_ofNat, Doubling.shift, h, negative]
  | negSucc n => simp [negative]

/-- Removing the parity bit exposes the exact natural payload, without division. -/
theorem encoding_tail (z : ℤ) : (encoding.encode z).tail = encodeNat (payload z) := by
  cases z with
  | ofNat n => cases h : encodeNat n <;> simp [encoding_ofNat, Doubling.shift, h, payload]
  | negSucc n => simp [payload]

@[simp] theorem payload_magnitude (z : ℤ) :
    payload z + (negative z).toNat = z.natAbs := by cases z <;> simp [payload, negative]

@[simp] theorem pairEncoding_length (p : ℤ × ℤ) :
    (pairEncoding.encode p).length =
      2 * (encoding.encode p.1).length + (encoding.encode p.2).length + 1 := by
  simp [pairEncoding]
  omega

/-- Temporary sign/magnitude is a semantic invariant, never an encoded-function opcode. -/
def ofSign (sign : Bool) (magnitude : ℕ) : ℤ :=
  if sign then -(magnitude : ℤ) else (magnitude : ℤ)

@[simp] theorem ofSign_negative_natAbs (z : ℤ) : ofSign (negative z) z.natAbs = z := by
  cases z <;> rfl

theorem ofSign_mul (a b : Bool) (m n : ℕ) :
    ofSign (xor a b) (m * n) = ofSign a m * ofSign b n := by
  cases a <;> cases b <;> simp [ofSign]

theorem signed_mul (a b : ℤ) : ofSign (xor (negative a) (negative b)) (a.natAbs * b.natAbs) = a * b := by
  rw [ofSign_mul, ofSign_negative_natAbs, ofSign_negative_natAbs]

end Holant.Complexity.IntegerArithmetic
