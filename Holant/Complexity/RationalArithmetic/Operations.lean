import Holant.Complexity.RationalArithmetic.ScalarMachines

/-! Actual canonical rational addition and multiplication. The finite programs
are assembled from literal-code unpairing, physical product wiring, signed and
natural arithmetic, normalized gcd/quotient reduction, and literal-code pairing.
All intermediate word-size costs come from proved machine transition bounds. -/
namespace Holant.Complexity.RationalArithmetic
open Computability BinaryCompose

noncomputable def firstComputes : Computes inputEncoding Holant.Algebraic.rationalEncoding Prod.fst :=
  FixedFieldMachines.Wiring.firstComputes _ _
noncomputable def secondComputes : Computes inputEncoding Holant.Algebraic.rationalEncoding Prod.snd :=
  FixedFieldMachines.Wiring.secondComputes _ _

noncomputable def leftNumeratorComputes :
    Computes inputEncoding IntegerArithmetic.encoding (fun p : ℚ × ℚ => p.1.num) :=
  FixedFieldMachines.congrComputes (firstComputes.andThen numeratorComputes) (fun _ => rfl)
noncomputable def rightNumeratorComputes :
    Computes inputEncoding IntegerArithmetic.encoding (fun p : ℚ × ℚ => p.2.num) :=
  FixedFieldMachines.congrComputes (secondComputes.andThen numeratorComputes) (fun _ => rfl)
noncomputable def leftDenominatorComputes :
    Computes inputEncoding encodingNatBool (fun p : ℚ × ℚ => p.1.den) :=
  FixedFieldMachines.congrComputes (firstComputes.andThen denominatorComputes) (fun _ => rfl)
noncomputable def rightDenominatorComputes :
    Computes inputEncoding encodingNatBool (fun p : ℚ × ℚ => p.2.den) :=
  FixedFieldMachines.congrComputes (secondComputes.andThen denominatorComputes) (fun _ => rfl)
noncomputable def leftDenominatorIntegerComputes :
    Computes inputEncoding IntegerArithmetic.encoding (fun p : ℚ × ℚ => (p.1.den : ℤ)) :=
  FixedFieldMachines.congrComputes (leftDenominatorComputes.andThen natCastComputes) (fun _ => rfl)
noncomputable def rightDenominatorIntegerComputes :
    Computes inputEncoding IntegerArithmetic.encoding (fun p : ℚ × ℚ => (p.2.den : ℤ)) :=
  FixedFieldMachines.congrComputes (rightDenominatorComputes.andThen natCastComputes) (fun _ => rfl)

/-- Positive denominator product, computed in ordinary canonical binary. -/
noncomputable def denominatorProductComputes :
    Computes inputEncoding encodingNatBool (fun p : ℚ × ℚ => p.1.den * p.2.den) :=
  FixedFieldMachines.congrComputes ((FixedFieldMachines.pairComputes
    leftDenominatorComputes rightDenominatorComputes).andThen naturalMultiplicationComputes) (fun _ => rfl)

noncomputable def numeratorProductComputes :
    Computes inputEncoding IntegerArithmetic.encoding (fun p : ℚ × ℚ => p.1.num * p.2.num) :=
  FixedFieldMachines.congrComputes ((FixedFieldMachines.pairComputes
    leftNumeratorComputes rightNumeratorComputes).andThen integerMultiplicationComputes) (fun _ => rfl)

noncomputable def leftCrossProductComputes :
    Computes inputEncoding IntegerArithmetic.encoding (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ)) :=
  FixedFieldMachines.congrComputes ((FixedFieldMachines.pairComputes
    leftNumeratorComputes rightDenominatorIntegerComputes).andThen integerMultiplicationComputes) (fun _ => rfl)

noncomputable def rightCrossProductComputes :
    Computes inputEncoding IntegerArithmetic.encoding (fun p : ℚ × ℚ => p.2.num * (p.1.den : ℤ)) :=
  FixedFieldMachines.congrComputes ((FixedFieldMachines.pairComputes
    rightNumeratorComputes leftDenominatorIntegerComputes).andThen integerMultiplicationComputes) (fun _ => rfl)

noncomputable def numeratorSumComputes :
    Computes inputEncoding IntegerArithmetic.encoding
      (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ) + p.2.num * (p.1.den : ℤ)) :=
  FixedFieldMachines.congrComputes ((FixedFieldMachines.pairComputes
    leftCrossProductComputes rightCrossProductComputes).andThen integerAdditionComputes) (fun _ => rfl)

/-- Full rational multiplication with the unchanged exact scalar input/output codec. -/
noncomputable def multiplicationComputes :
    Computes inputEncoding Holant.Algebraic.rationalEncoding (fun p : ℚ × ℚ => p.1 * p.2) :=
  FixedFieldMachines.congrComputes ((FixedFieldMachines.pairComputes
    numeratorProductComputes denominatorProductComputes).andThen normalizationForwardComputes)
    (fun p => (Rat.mul_eq_mkRat p.1 p.2).symm)

/-- Full rational addition, including exact cancellation and canonical zero. -/
noncomputable def additionComputes :
    Computes inputEncoding Holant.Algebraic.rationalEncoding (fun p : ℚ × ℚ => p.1 + p.2) :=
  FixedFieldMachines.congrComputes ((FixedFieldMachines.pairComputes
    numeratorSumComputes denominatorProductComputes).andThen normalizationForwardComputes)
    (fun p => (Rat.add_def' p.1 p.2).symm)

noncomputable def multiplicationPolyTime : PolyTime inputEncoding Holant.Algebraic.rationalEncoding
    (fun p : ℚ × ℚ => p.1 * p.2) := multiplicationComputes.toPolyTime
noncomputable def additionPolyTime : PolyTime inputEncoding Holant.Algebraic.rationalEncoding
    (fun p : ℚ × ℚ => p.1 + p.2) := additionComputes.toPolyTime

theorem multiplication_inFP : InFP inputEncoding Holant.Algebraic.rationalEncoding
    (fun p : ℚ × ℚ => p.1 * p.2) := multiplicationComputes.inFP
theorem addition_inFP : InFP inputEncoding Holant.Algebraic.rationalEncoding
    (fun p : ℚ × ℚ => p.1 + p.2) := additionComputes.inFP

end Holant.Complexity.RationalArithmetic
