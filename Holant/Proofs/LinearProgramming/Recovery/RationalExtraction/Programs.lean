import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.DivMod
import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Jump

set_option autoImplicit false

/-! Kernel-checked recovery component. One complete accelerated Stern--Brocot block is assembled
from finite integer/rational programs. Both quotient and remainder run on the
actual cross-product words. No continued-fraction computation is a host opcode.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Programs
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution.Compiler
noncomputable section

def query : Computes stepEncoding queryEncoding (fun v : StepInput => v.1) := Wiring.firstComputes _ _
def endpoints : Computes stepEncoding RationalArithmetic.inputEncoding (fun v : StepInput => v.1.1) :=
  query.andThen (Wiring.firstComputes _ _)
def lower : Computes stepEncoding rationalEncoding (fun v : StepInput => lo v.1) :=
  endpoints.andThen RationalArithmetic.firstComputes
def upper : Computes stepEncoding rationalEncoding (fun v : StepInput => hi v.1) :=
  endpoints.andThen RationalArithmetic.secondComputes
def bound : Computes stepEncoding encodingNatBool (fun v : StepInput => cap v.1) :=
  query.andThen (Wiring.secondComputes _ _)
def pair : Computes stepEncoding neighborsEncoding (fun v : StepInput => v.2) := Wiring.secondComputes _ _
def left : Computes stepEncoding fractionEncoding (fun v : StepInput => v.2.1) :=
  pair.andThen (Wiring.firstComputes _ _)
def right : Computes stepEncoding fractionEncoding (fun v : StepInput => v.2.2) :=
  pair.andThen (Wiring.secondComputes _ _)
def a : Computes stepEncoding IntegerArithmetic.encoding (fun v : StepInput => v.2.1.1) :=
  left.andThen (Wiring.firstComputes _ _)
def b : Computes stepEncoding encodingNatBool (fun v : StepInput => v.2.1.2) :=
  left.andThen (Wiring.secondComputes _ _)
def c : Computes stepEncoding IntegerArithmetic.encoding (fun v : StepInput => v.2.2.1) :=
  right.andThen (Wiring.firstComputes _ _)
def d : Computes stepEncoding encodingNatBool (fun v : StepInput => v.2.2.2) :=
  right.andThen (Wiring.secondComputes _ _)
def bInt := b.andThen RationalArithmetic.natCastComputes
def dInt := d.andThen RationalArithmetic.natCastComputes

def intAdd {f g : StepInput → ℤ}
    (u : Computes stepEncoding IntegerArithmetic.encoding f)
    (v : Computes stepEncoding IntegerArithmetic.encoding g) :
    Computes stepEncoding IntegerArithmetic.encoding (fun x => f x+g x) :=
  (pairComputes u v).andThen RationalArithmetic.integerAdditionComputes
def intMul {f g : StepInput → ℤ}
    (u : Computes stepEncoding IntegerArithmetic.encoding f)
    (v : Computes stepEncoding IntegerArithmetic.encoding g) :
    Computes stepEncoding IntegerArithmetic.encoding (fun x => f x*g x) :=
  (pairComputes u v).andThen RationalArithmetic.integerMultiplicationComputes
def intSub {f g : StepInput → ℤ}
    (u : Computes stepEncoding IntegerArithmetic.encoding f)
    (v : Computes stepEncoding IntegerArithmetic.encoding g) :
    Computes stepEncoding IntegerArithmetic.encoding (fun x => f x-g x) :=
  (pairComputes u v).andThen Comparison.integerDifference
def natAdd {f g : StepInput → ℕ}
    (u : Computes stepEncoding encodingNatBool f) (v : Computes stepEncoding encodingNatBool g) :
    Computes stepEncoding encodingNatBool (fun x => f x+g x) :=
  (pairComputes u v).andThen Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.addComputes
def natMul {f g : StepInput → ℕ}
    (u : Computes stepEncoding encodingNatBool f) (v : Computes stepEncoding encodingNatBool g) :
    Computes stepEncoding encodingNatBool (fun x => f x*g x) :=
  (pairComputes u v).andThen RationalArithmetic.naturalMultiplicationComputes

def lowerNumerator := lower.andThen RationalArithmetic.numeratorComputes
def lowerDenominatorInt :=
  (lower.andThen RationalArithmetic.denominatorComputes).andThen RationalArithmetic.natCastComputes
def upperNumerator := upper.andThen RationalArithmetic.numeratorComputes
def upperDenominatorInt :=
  (upper.andThen RationalArithmetic.denominatorComputes).andThen RationalArithmetic.natCastComputes
def Nlo : Computes stepEncoding IntegerArithmetic.encoding
    (fun v : StepInput => Fraction.lowerCross (lo v.1) v.2.1) :=
  intSub (intMul lowerNumerator bInt) (intMul a lowerDenominatorInt)
def Klo : Computes stepEncoding IntegerArithmetic.encoding
    (fun v : StepInput => Fraction.upperCross (lo v.1) v.2.2) :=
  intSub (intMul c lowerDenominatorInt) (intMul lowerNumerator dInt)
def Nhi : Computes stepEncoding IntegerArithmetic.encoding
    (fun v : StepInput => Fraction.lowerCross (hi v.1) v.2.1) :=
  intSub (intMul upperNumerator bInt) (intMul a upperDenominatorInt)
def Khi : Computes stepEncoding IntegerArithmetic.encoding
    (fun v : StepInput => Fraction.upperCross (hi v.1) v.2.2) :=
  intSub (intMul c upperDenominatorInt) (intMul upperNumerator dInt)

def factor {f g : StepInput → ℤ}
    (u : Computes stepEncoding IntegerArithmetic.encoding f)
    (v : Computes stepEncoding IntegerArithmetic.encoding g) :
    Computes stepEncoding encodingNatBool (fun x => DivMod.jump (f x).toNat (g x).toNat) :=
  (pairComputes
    ((pairComputes (u.andThen RoundingProgram.toNat)
      (constantComputes stepEncoding encodingNatBool 1)).andThen Endpoints.subtractComputes)
    (v.andThen RoundingProgram.toNat)).andThen
      (DivMod.computes.andThen (Wiring.firstComputes _ _))
def leftFactor : Computes stepEncoding encodingNatBool
    (fun v : StepInput => Jump.leftFactor v.1 v.2) := factor Nlo Klo
def rightFactor : Computes stepEncoding encodingNatBool
    (fun v : StepInput => Jump.rightFactor v.1 v.2) := factor Khi Nhi

def leftJump : Computes stepEncoding neighborsEncoding
    (fun v : StepInput => Neighbors.leftJump v.2 (Jump.leftFactor v.1 v.2)) :=
  pairComputes
    (pairComputes (intAdd a (intMul (leftFactor.andThen RationalArithmetic.natCastComputes) c))
      (natAdd b (natMul leftFactor d))) right
def rightJump : Computes stepEncoding neighborsEncoding
    (fun v : StepInput => Neighbors.rightJump v.2 (Jump.rightFactor v.1 v.2)) :=
  pairComputes left
    (pairComputes (intAdd c (intMul (rightFactor.andThen RationalArithmetic.natCastComputes) a))
      (natAdd d (natMul rightFactor b)))
def middle : Computes stepEncoding fractionEncoding (fun v : StepInput => Neighbors.middle v.2) :=
  pairComputes (intAdd a c) (natAdd b d)
def value : Computes stepEncoding rationalEncoding (fun v : StepInput => Fraction.value (Neighbors.middle v.2)) :=
  middle.andThen RationalArithmetic.normalizationForwardComputes
def excluded : Computes stepEncoding encodingBoolBool
    (fun v : StepInput => decide (cap v.1<v.2.1.2+v.2.2.2)) :=
  (pairComputes bound (natAdd b d)).andThen Endpoints.lessComputes
def goLeft : Computes stepEncoding encodingBoolBool
    (fun v : StepInput => decide (Fraction.value (Neighbors.middle v.2)<lo v.1)) :=
  (pairComputes value lower).andThen Comparison.rationalLess
def goRight : Computes stepEncoding encodingBoolBool
    (fun v : StepInput => decide (hi v.1<Fraction.value (Neighbors.middle v.2))) :=
  (pairComputes upper value).andThen Comparison.rationalLess

def emit {f : StepInput → Neighbors} (doneBit foundBit : Bool)
    (u : Computes stepEncoding rationalEncoding (fun _ : StepInput => (0:ℚ)))
    (v : Computes stepEncoding neighborsEncoding f) :
    Computes stepEncoding resultEncoding (fun x => ((doneBit,foundBit),(0,f x))) :=
  pairComputes (pairComputes (constantComputes stepEncoding encodingBoolBool doneBit)
    (constantComputes stepEncoding encodingBoolBool foundBit)) (pairComputes u v)
def zero := constantComputes stepEncoding rationalEncoding (0:ℚ)
def emitNone : Computes stepEncoding resultEncoding (fun v : StepInput => miss v.2) := emit true false zero pair
def emitLeft : Computes stepEncoding resultEncoding
    (fun v : StepInput => pending (Neighbors.leftJump v.2 (Jump.leftFactor v.1 v.2))) :=
  emit false false zero leftJump
def emitRight : Computes stepEncoding resultEncoding
    (fun v : StepInput => pending (Neighbors.rightJump v.2 (Jump.rightFactor v.1 v.2))) :=
  emit false false zero rightJump
def emitSome : Computes stepEncoding resultEncoding
    (fun v : StepInput => hit (Fraction.value (Neighbors.middle v.2)) v.2) :=
  pairComputes (pairComputes (constantComputes stepEncoding encodingBoolBool true)
    (constantComputes stepEncoding encodingBoolBool true)) (pairComputes value pair)

def computes : Computes stepEncoding resultEncoding Jump.step :=
  congrComputes (ifComputes excluded emitNone
    (ifComputes goLeft emitLeft (ifComputes goRight emitRight emitSome)))
    (fun v => by simp [Jump.step])

end
end Programs
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
