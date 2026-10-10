import Holant.Complexity.RationalArithmetic.Execution

/-! Linear-size reset-state observers for the actual nested Boolean registers.
These functions are test instrumentation, never machine instructions. Their
correctness is proved structurally, without enumerating the finite state space. -/
namespace Holant.Complexity.RationalArithmetic
open FixedFieldMachines

structure StateCheck (m : RawMachine) where
  inspect : m.State → Bool
  correct : ∀ state, inspect state = true ↔ state = m.initial

namespace StateCheck

def ofEq (m : RawMachine) [DecidableEq m.State] : StateCheck m where
  inspect state := decide (state = m.initial)
  correct _ := by simp

def compose {a b : RawMachine} (ha : StateCheck a) (hb : StateCheck b) : StateCheck (a.compose b) where
  inspect state := state.1.isNone && ha.inspect state.2.1 && hb.inspect state.2.2
  correct state := by
    rcases state with ⟨bit, sa, sb⟩
    simp [RawMachine.compose, Bool.and_eq_true, ha.correct, hb.correct, and_assoc]

def leftMap {m : RawMachine} (h : StateCheck m) : StateCheck m.leftMap where
  inspect state := state.1.isNone && h.inspect state.2
  correct state := by
    rcases state with ⟨bit, state⟩
    simp [RawMachine.leftMap, Bool.and_eq_true, h.correct]

def swap : StateCheck (RawMachine.erase Wiring.swapMachine) := @ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def first : StateCheck (RawMachine.erase Wiring.firstMachine) := @ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def diagonal : StateCheck (RawMachine.erase Wiring.diagonalMachine) := @ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def reverse : StateCheck (RawMachine.erase Reverse.machine) := @ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def second : StateCheck Execution.second := swap.compose first

def rightMap {m : RawMachine} (h : StateCheck m) : StateCheck m.rightMap :=
  (swap.compose h.leftMap).compose swap

def pair {a b : RawMachine} (ha : StateCheck a) (hb : StateCheck b) : StateCheck (a.pair b) :=
  (diagonal.compose ha.leftMap).compose hb.rightMap

end StateCheck

namespace Execution

def checkReversePair : StateCheck reversePair := StateCheck.reverse.leftMap.compose StateCheck.reverse.rightMap
def checkIntegerAdd : StateCheck integerAdd := checkReversePair.compose (@StateCheck.ofEq (RawMachine.erase integerAdditionMachine) (inferInstanceAs (DecidableEq IntegerArithmetic.Addition.Memory)))
def checkIntegerMul : StateCheck integerMul := checkReversePair.compose (@StateCheck.ofEq (RawMachine.erase integerMultiplicationMachine) (inferInstanceAs (DecidableEq IntegerArithmetic.Multiplication.Memory)))
def checkNaturalMul : StateCheck naturalMul := checkReversePair.compose (@StateCheck.ofEq (RawMachine.erase naturalMultiplicationMachine) (inferInstanceAs (DecidableEq BinaryArithmetic.EncodedMultiplication.Memory)))
def checkComponents : StateCheck components :=
  ((@StateCheck.ofEq (RawMachine.erase unpairMachine) (inferInstanceAs (DecidableEq BinaryArithmetic.Unpairing.Memory))).compose StateCheck.reverse.leftMap).compose StateCheck.reverse.rightMap
def checkNumerator : StateCheck numerator := checkComponents.compose StateCheck.first
def checkDenominator : StateCheck denominator := checkComponents.compose StateCheck.second
def checkPackedNormalization : StateCheck packedNormalization :=
  (@StateCheck.ofEq (RawMachine.erase Normalization.machine) (inferInstanceAs (DecidableEq Normalization.Memory))).compose (@StateCheck.ofEq (RawMachine.erase pairingMachine) (inferInstanceAs (DecidableEq BinaryArithmetic.EncodedPairing.Memory)))
def checkNormalize : StateCheck normalize := checkReversePair.compose checkPackedNormalization
def checkLeftNumerator : StateCheck leftNumerator := StateCheck.first.compose checkNumerator
def checkRightNumerator : StateCheck rightNumerator := StateCheck.second.compose checkNumerator
def checkLeftDenominator : StateCheck leftDenominator := StateCheck.first.compose checkDenominator
def checkRightDenominator : StateCheck rightDenominator := StateCheck.second.compose checkDenominator
def checkLeftDenominatorInteger : StateCheck leftDenominatorInteger :=
  checkLeftDenominator.compose (@StateCheck.ofEq (RawMachine.erase natCastMachine) (inferInstanceAs (DecidableEq (Option Bool))))
def checkRightDenominatorInteger : StateCheck rightDenominatorInteger :=
  checkRightDenominator.compose (@StateCheck.ofEq (RawMachine.erase natCastMachine) (inferInstanceAs (DecidableEq (Option Bool))))
def checkDenominatorProduct : StateCheck denominatorProduct := (checkLeftDenominator.pair checkRightDenominator).compose checkNaturalMul
def checkNumeratorProduct : StateCheck numeratorProduct := (checkLeftNumerator.pair checkRightNumerator).compose checkIntegerMul
def checkLeftCrossProduct : StateCheck leftCrossProduct := (checkLeftNumerator.pair checkRightDenominatorInteger).compose checkIntegerMul
def checkRightCrossProduct : StateCheck rightCrossProduct := (checkRightNumerator.pair checkLeftDenominatorInteger).compose checkIntegerMul
def checkNumeratorSum : StateCheck numeratorSum := (checkLeftCrossProduct.pair checkRightCrossProduct).compose checkIntegerAdd
def checkMultiplication : StateCheck multiplication := (checkNumeratorProduct.pair checkDenominatorProduct).compose checkNormalize
def checkAddition : StateCheck addition := (checkNumeratorSum.pair checkDenominatorProduct).compose checkNormalize

end Execution
end Holant.Complexity.RationalArithmetic
