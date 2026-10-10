import Mathlib.Computability.Encoding
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact binary rational and fixed-vector encodings

A rational is encoded using its canonical integer numerator and positive natural
denominator, paired as a natural and written in binary. No decimal approximation
or classical equality decision occurs in the codec. Coefficient vectors use an
explicit self-delimiting bit framing, whose overhead is proved below.
-/

namespace Holant.Algebraic

open Computability

/-- Signed numerator and positive denominator packed with the explicit natural
pairing bijection. -/
def rationalCode (q : ℚ) : ℕ := Nat.pair (Equiv.intEquivNat q.num) q.den

/-- Decode a rational pair, rejecting a zero denominator. Noncanonical fractions
are harmlessly normalized by exact rational arithmetic. -/
def rationalDecode (n : ℕ) : Option ℚ :=
  let p := Nat.unpair n
  if p.2 = 0 then none else some (mkRat (Equiv.intEquivNat.symm p.1) p.2)

@[simp] theorem rationalDecode_code (q : ℚ) : rationalDecode (rationalCode q) = some q := by
  simp [rationalDecode, rationalCode, q.den_nz]

/-- Binary scalar encoding, with a verified decoder left inverse. -/
def rationalEncoding : Encoding ℚ Bool where
  encode q := encodeNat (rationalCode q)
  decode bits := rationalDecode (decodeNat bits)
  decode_encode q := by simp

theorem rationalEncoding_injective : Function.Injective rationalEncoding.encode :=
  rationalEncoding.encode_injective

/-- A bit string is framed by `true, bit` pairs and a final `false` delimiter. -/
def frame : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: frame bs

/-- Parse exactly one framed string, returning the unconsumed suffix. -/
def unframe : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: rest => some ([], rest)
  | true :: [] => none
  | true :: b :: rest => (unframe rest).map (fun p => (b :: p.1, p.2))

@[simp] theorem unframe_frame_append (bits suffix : List Bool) :
    unframe (frame bits ++ suffix) = some (bits, suffix) := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simpa [frame, unframe] using congrArg (Option.map (fun p => (b :: p.1, p.2))) ih

@[simp] theorem frame_length (bits : List Bool) : (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [frame, List.length_cons, ih]
    omega

/-- Encode an ordered fixed-dimensional rational coefficient vector. -/
def vectorEncode : (n : ℕ) → (Fin n → ℚ) → List Bool
  | 0, _ => []
  | n + 1, v => frame (rationalEncoding.encode (v 0)) ++ vectorEncode n (Fin.tail v)

/-- Decode a known number of rational coefficients, retaining the suffix. -/
def vectorDecodePrefix : (n : ℕ) → List Bool → Option ((Fin n → ℚ) × List Bool)
  | 0, bits => some (Fin.elim0, bits)
  | n + 1, bits => do
    let (head, rest) ← unframe bits
    let q ← rationalEncoding.decode head
    let (v, suffix) ← vectorDecodePrefix n rest
    pure (Fin.cons q v, suffix)

@[simp] theorem vectorDecodePrefix_encode_append (n : ℕ) (v : Fin n → ℚ) (suffix : List Bool) :
    vectorDecodePrefix n (vectorEncode n v ++ suffix) = some (v, suffix) := by
  induction n with
  | zero =>
    have hv : (Fin.elim0 : Fin 0 → ℚ) = v := funext (fun i => Fin.elim0 i)
    simp [vectorDecodePrefix, vectorEncode, hv]
  | succ n ih =>
    simp [vectorDecodePrefix, vectorEncode, List.append_assoc, ih]

/-- A full vector code cannot silently contain trailing coefficients. -/
def vectorEncoding (n : ℕ) : Encoding (Fin n → ℚ) Bool where
  encode := vectorEncode n
  decode bits := (vectorDecodePrefix n bits).bind (fun p => if p.2 = [] then some p.1 else none)
  decode_encode v := by
    have h := vectorDecodePrefix_encode_append n v []
    simpa using congrArg (fun x => x.bind (fun p => if p.2 = [] then some p.1 else none)) h

/-- Framing has linear overhead in the total scalar code length. -/
theorem vectorEncode_length (n : ℕ) (v : Fin n → ℚ) :
    (vectorEncode n v).length = ∑ i, (2 * (rationalEncoding.encode (v i)).length + 1) := by
  induction n with
  | zero => simp [vectorEncode]
  | succ n ih => simp [vectorEncode, ih, Fin.sum_univ_succ, Fin.tail]

end Holant.Algebraic
