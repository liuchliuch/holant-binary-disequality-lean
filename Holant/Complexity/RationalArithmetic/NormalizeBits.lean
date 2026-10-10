import Holant.Complexity.BinaryArithmetic.GcdBits
import Holant.Complexity.IntegerArithmetic.CarryBits
import Mathlib.Data.Rat.Defs

/-! Pure bit-list specification for canonical rational normalization. Gcd and
quotients are computed by the existing binary recurrences. This specification
contains no division, gcd, or rational-normalization opcode and claims no time
bound independently of its operational compilation. -/

namespace Holant.Complexity.RationalArithmetic
open Computability BinaryArithmetic IntegerArithmetic

/-- A signed numerator and natural denominator retain their literal component
codes. This intermediate input is distinct from the established rational code. -/
def fractionEncoding : Encoding (ℤ × ℕ) Bool where
  encode p := Holant.Algebraic.frame (encoding.encode p.1).reverse ++ (encodeNat p.2).reverse
  decode bits := (Holant.Algebraic.unframe bits).map fun p =>
    (Equiv.intEquivNat.symm (decodeNat p.1.reverse), decodeNat p.2.reverse)
  decode_encode p := by simp [encoding]

@[simp] theorem fractionEncoding_length (p : ℤ × ℕ) :
    (fractionEncoding.encode p).length =
      2 * (encoding.encode p.1).length + (encodeNat p.2).length + 1 := by
  simp [fractionEncoding]; omega

/-- Canonical numerator-code and denominator bits, including mkRat's zero
convention for a zero denominator. -/
def normalizeBits (sign : Bool) (magnitude denominator : List Bool) : List Bool × List Bool :=
  if denominator = [] then ([], [true]) else
    let g := GcdBits.gcdBits magnitude denominator
    (recode sign (DivisionBits.divideBits magnitude.reverse g).1,
      (DivisionBits.divideBits denominator.reverse g).1)

@[simp] theorem natAbs_ofSign (sign : Bool) (n : ℕ) : (ofSign sign n).natAbs = n := by
  cases sign <;> simp [ofSign]

theorem ofSign_div_of_dvd (sign : Bool) (n d : ℕ) (h : d ∣ n) :
    ofSign sign (n / d) = ofSign sign n / (d : ℤ) := by
  cases sign
  · simp [ofSign]
  · simp only [ofSign, ↓reduceIte]
    rw [Int.neg_ediv_of_dvd (Int.natCast_dvd_natCast.mpr h)]
    rfl

/-- The chosen signed quotient is exact because the gcd divides the magnitude. -/
theorem mkRat_num_ofSign (sign : Bool) (n d : ℕ) (hd : d ≠ 0) :
    (mkRat (ofSign sign n) d).num = ofSign sign (n / Nat.gcd n d) := by
  simp only [Rat.num_mkRat, hd, ↓reduceIte, natAbs_ofSign]
  rw [Nat.gcd_comm, ← ofSign_div_of_dvd sign n (Nat.gcd n d) (Nat.gcd_dvd_left n d)]

theorem mkRat_den_ofSign (sign : Bool) (n d : ℕ) (hd : d ≠ 0) :
    (mkRat (ofSign sign n) d).den = d / Nat.gcd n d := by
  simp [Rat.den_mkRat, hd, Nat.gcd_comm]

/-- Complete literal-code specification; denominator zero yields numerator zero
and denominator one, never an empty rational scalar code. -/
theorem normalizeBits_encodeNat (sign : Bool) (n d : ℕ) :
    normalizeBits sign (encodeNat n) (encodeNat d) =
      (encoding.encode (mkRat (ofSign sign n) d).num,
        encodeNat (mkRat (ofSign sign n) d).den) := by
  by_cases hd : d = 0
  · subst d
    change ([], [true]) = (encoding.encode 0, encodeNat 1)
    rfl
  · simp only [normalizeBits, encodeNat_eq_nil, hd, ↓reduceIte,
      GcdBits.gcdBits_encodeNat, DivisionBits.divideBits_encodeNat,
      recode_encodeNat, mkRat_num_ofSign sign n d hd, mkRat_den_ofSign sign n d hd]

theorem normalizeBits_integer (n : ℤ) (d : ℕ) :
    normalizeBits (negative n) (encodeNat n.natAbs) (encodeNat d) =
      (encoding.encode (mkRat n d).num, encodeNat (mkRat n d).den) := by
  simpa using normalizeBits_encodeNat (negative n) n.natAbs d

/-- The output components are canonical binary words. -/
theorem canonical_normalizeBits (sign : Bool) (n d : ℕ) :
    Canonical (normalizeBits sign (encodeNat n) (encodeNat d)).1 ∧
    Canonical (normalizeBits sign (encodeNat n) (encodeNat d)).2 := by
  rw [normalizeBits_encodeNat]
  exact ⟨canonical_encodeNat _, canonical_encodeNat _⟩

theorem normalizeBits_den_positive (sign : Bool) (n d : ℕ) :
    0 < value (normalizeBits sign (encodeNat n) (encodeNat d)).2 := by
  rw [normalizeBits_encodeNat]
  simpa using (mkRat (ofSign sign n) d).den_pos

end Holant.Complexity.RationalArithmetic
