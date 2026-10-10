import Holant.Complexity.RationalArithmetic.Operations
import Mathlib.Tactic.FieldSimp

/-! Canonical rational inversion, including zero, by actual existing signed
arithmetic and normalization machines. The only new bit operation removes the
known nonnegative parity bit in one transition. -/
namespace Holant.Complexity.RationalArithmetic
open Turing Computability BinaryCompose BinaryArithmetic FixedFieldMachines
noncomputable section
set_option backward.isDefEq.respectTransparency false

def doubledNatEncoding : Encoding ℕ Bool where
  encode n := IntegerArithmetic.encoding.encode (n:ℤ)
  decode bits := some (decodeNat bits.tail)
  decode_encode n := by
    change some (decodeNat ((IntegerArithmetic.encoding.encode (n:ℤ)).tail))=some n
    rw [IntegerArithmetic.encoding_tail]
    simp [IntegerArithmetic.payload]

abbrev tailMachine : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  program _ := .pop () (fun _ _ => ()) .halt

theorem tailMachine_step (bits : List Bool) :
    tailMachine.computer.step (initList tailMachine.computer bits)=
      some (haltList tailMachine.computer bits.tail) := by
  cases bits <;> simp [FinTM2.step,TM2.step,tailMachine,initList,haltList,TM2.stepAux]
  all_goals rfl

def removeParityComputes : Computes doubledNatEncoding encodingNatBool id where
  machine := tailMachine
  time := 1
  outputs n := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := by simp }
    change tailMachine.computer.step
      (initList tailMachine.computer (IntegerArithmetic.encoding.encode (n:ℤ)))=
        some (haltList tailMachine.computer (encodeNat n))
    have h := tailMachine_step (IntegerArithmetic.encoding.encode (n:ℤ))
    rw [IntegerArithmetic.encoding_tail] at h
    exact h

def numeratorSquareComputes : Computes Holant.Algebraic.rationalEncoding
    IntegerArithmetic.encoding (fun q : ℚ => q.num*q.num) :=
  congrComputes ((pairComputes numeratorComputes numeratorComputes).andThen
    integerMultiplicationComputes) (fun _ => rfl)

def squareMagnitudeComputes : Computes Holant.Algebraic.rationalEncoding encodingNatBool
    (fun q : ℚ => q.num.natAbs^2) := by
  have code : Computes Holant.Algebraic.rationalEncoding doubledNatEncoding
      (fun q : ℚ => q.num.natAbs^2) :=
    recode numeratorSquareComputes id (fun _ => rfl) (fun q => by
      change IntegerArithmetic.encoding.encode (q.num*q.num)=
        IntegerArithmetic.encoding.encode ((q.num.natAbs^2:ℕ):ℤ)
      congr 1
      simp [Int.natCast_pow,Int.natCast_natAbs,sq_abs,pow_two])
  exact congrComputes (code.andThen removeParityComputes) (fun _ => rfl)

def inverseNumeratorComputes : Computes Holant.Algebraic.rationalEncoding
    IntegerArithmetic.encoding (fun q : ℚ => q.num*(q.den:ℤ)) :=
  congrComputes ((pairComputes numeratorComputes denominatorIntegerComputes).andThen
    integerMultiplicationComputes) (fun _ => rfl)

theorem inverse_fraction (q : ℚ) : mkRat (q.num*(q.den:ℤ)) (q.num.natAbs^2)=q⁻¹ := by
  have hs : ((q.num.natAbs^2:ℕ):ℚ)=(q.num:ℚ)^2 := by
    have h : ((q.num.natAbs^2:ℕ):ℤ)=q.num^2 := by
      simp [Int.natCast_pow,Int.natCast_natAbs,sq_abs]
    simpa only [Int.cast_natCast,Int.cast_pow] using congrArg (fun z : ℤ => (z:ℚ)) h
  rw [Rat.mkRat_eq_div,Int.cast_mul,Int.cast_natCast,hs]
  by_cases hz : q=0
  · subst q; norm_num
  · have hn : (q.num:ℚ)≠0 := by exact_mod_cast Rat.num_ne_zero.mpr hz
    have hd : (q.den:ℚ)≠0 := by exact_mod_cast q.den_ne_zero
    conv_rhs => rw [←Rat.num_div_den q]
    field_simp

/-- Total inverse on the unchanged canonical rational encoding. No primitive
field-inverse instruction or supplied reciprocal provider is used. -/
def inverseComputes : Computes Holant.Algebraic.rationalEncoding Holant.Algebraic.rationalEncoding
    (fun q : ℚ => q⁻¹) :=
  congrComputes ((pairComputes inverseNumeratorComputes squareMagnitudeComputes).andThen
    normalizationForwardComputes) inverse_fraction

theorem inverse_inFP : InFP Holant.Algebraic.rationalEncoding Holant.Algebraic.rationalEncoding
    (fun q : ℚ => q⁻¹) := inverseComputes.inFP

end
end Holant.Complexity.RationalArithmetic
