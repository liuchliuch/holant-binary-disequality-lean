import Holant.Proofs.LinearProgramming.Foundation.Parsing
import Holant.Proofs.LinearProgramming.Foundation.Infrastructure.BitReadInterface
import Holant.Proofs.LinearProgramming.Foundation.Infrastructure.RationalInverse

open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure

/-! Rational LP foundation adapted into the exclusive task namespace.
Exact signed and rational comparison, using physical canonical-code operations.
The padded sign read covers the empty encoding of zero. Copies, framing,
integer subtraction, rational normalization and clean output are all charged
by the composed machines. No comparison or LP oracle is introduced.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Comparison
open Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
noncomputable section

def signInput (z : ℤ) : BitRead.Input :=
  ⟨IntegerArithmetic.encoding.encode z ++ [false], ⟨0, by simp⟩⟩

def signInputComputes : Computes IntegerArithmetic.encoding BitRead.inputEncoding signInput := by
  let padded := joinComputes (encodeComputes IntegerArithmetic.encoding)
    (constantComputes IntegerArithmetic.encoding Frame.wordEncoding [false])
  exact recode (pairComputes padded
    (constantComputes IntegerArithmetic.encoding UnaryBinary.unaryEncoding 0))
    id (fun _ => rfl) (fun _ => rfl)

theorem signInput_value (z : ℤ) : BitRead.value (signInput z) = IntegerArithmetic.negative z := by
  have hh := IntegerArithmetic.encoding_head z
  cases hw : IntegerArithmetic.encoding.encode z <;>
    simpa [signInput, BitRead.value, hw] using hh

def negative : Computes IntegerArithmetic.encoding encodingBoolBool IntegerArithmetic.negative :=
  congrComputes (signInputComputes.andThen BitRead.computes) signInput_value

theorem negative_eq (z : ℤ) : IntegerArithmetic.negative z = decide (z < 0) := by
  cases z <;> simp [IntegerArithmetic.negative]

def integerLessZero : Computes IntegerArithmetic.encoding encodingBoolBool (fun z => decide (z < 0)) :=
  congrComputes negative negative_eq

def integerNegate : Computes IntegerArithmetic.encoding IntegerArithmetic.encoding Neg.neg :=
  congrComputes ((pairComputes (identityComputes IntegerArithmetic.encoding)
    (constantComputes IntegerArithmetic.encoding IntegerArithmetic.encoding (-1))).andThen
      RationalArithmetic.integerMultiplicationComputes) (fun z => by dsimp only [Function.comp_apply,id_eq]; ring)

def integerDifference : Computes (pairEncoding IntegerArithmetic.encoding IntegerArithmetic.encoding)
    IntegerArithmetic.encoding (fun p => p.1 - p.2) :=
  congrComputes ((pairComputes (Wiring.firstComputes _ _)
    ((Wiring.secondComputes _ _).andThen integerNegate)).andThen
      RationalArithmetic.integerAdditionComputes) (fun p => by dsimp only [Function.comp_apply]; ring)

def integerLess : Computes (pairEncoding IntegerArithmetic.encoding IntegerArithmetic.encoding)
    encodingBoolBool (fun p => decide (p.1 < p.2)) :=
  congrComputes (integerDifference.andThen integerLessZero) (fun p => by simp)

def rationalNegate : Computes Holant.Algebraic.rationalEncoding Holant.Algebraic.rationalEncoding Neg.neg :=
  congrComputes ((pairComputes (identityComputes Holant.Algebraic.rationalEncoding)
    (constantComputes Holant.Algebraic.rationalEncoding Holant.Algebraic.rationalEncoding (-1))).andThen
      RationalArithmetic.multiplicationComputes) (fun q => by dsimp only [Function.comp_apply,id_eq]; ring)

def rationalDifference : Computes RationalArithmetic.inputEncoding Holant.Algebraic.rationalEncoding
    (fun p => p.1 - p.2) :=
  congrComputes ((pairComputes RationalArithmetic.firstComputes
    (RationalArithmetic.secondComputes.andThen rationalNegate)).andThen
      RationalArithmetic.additionComputes) (fun p => by dsimp only [Function.comp_apply]; ring)

theorem numerator_negative (q : ℚ) : q.num < 0 ↔ q < 0 := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hc : (q.num : ℚ) < 0 ↔ q < 0 := by
    calc
      (q.num : ℚ) < 0 ↔ (q.num : ℚ) / q.den < 0 :=
        by simpa only [zero_mul] using (div_lt_iff₀ (b := (q.num : ℚ)) (a := 0) hd).symm
      _ ↔ q < 0 := by rw [Rat.num_div_den]
  constructor
  · intro h; exact hc.mp (by exact_mod_cast h)
  · intro h; exact_mod_cast hc.mpr h

def rationalLessZero : Computes Holant.Algebraic.rationalEncoding encodingBoolBool
    (fun q => decide (q < 0)) :=
  congrComputes (RationalArithmetic.numeratorComputes.andThen integerLessZero)
    (fun q => by change decide (q.num < 0) = decide (q < 0); exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using numerator_negative q))

def rationalLess : Computes RationalArithmetic.inputEncoding encodingBoolBool
    (fun p => decide (p.1 < p.2)) :=
  congrComputes (rationalDifference.andThen rationalLessZero) (fun p => by simp)

def rationalLe : Computes RationalArithmetic.inputEncoding encodingBoolBool
    (fun p => decide (p.1 ≤ p.2)) := by
  let swapped := pairComputes RationalArithmetic.secondComputes RationalArithmetic.firstComputes
  let lt := swapped.andThen rationalLess
  exact congrComputes (AccessPrograms.bool (fun a _ => !a) lt
    (constantComputes RationalArithmetic.inputEncoding encodingBoolBool false)) (fun p => by
      change (!decide (p.2 < p.1)) = decide (p.1 ≤ p.2)
      rw [← decide_not]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact not_lt)

/-- A standalone scalar subroutine, not existential positivity of an LP. -/
def rationalPositive : Computes Holant.Algebraic.rationalEncoding encodingBoolBool
    (fun q => decide (0 < q)) :=
  (pairComputes (constantComputes Holant.Algebraic.rationalEncoding Holant.Algebraic.rationalEncoding 0)
    (identityComputes Holant.Algebraic.rationalEncoding)).andThen rationalLess

theorem primitive_bound (p : ℚ × ℚ) :
    primitiveCost rationalLess.machine (rationalLess.outputs p).steps
      (some (Turing.initList rationalLess.machine.computer (RationalArithmetic.inputEncoding.encode p))) ≤
        (primitivePolynomial rationalLess).eval (RationalArithmetic.inputEncoding.encode p).length :=
  computes_primitive_cost rationalLess p

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Comparison
