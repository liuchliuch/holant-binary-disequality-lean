import Holant.Complexity.RationalArithmetic.Syntax
import Holant.Complexity.FixedFieldMachines.RawMachine

/-! Execution-only projections of the complete rational programs. The erased
records omit only unused finite-state/label enumeration metadata. Their keys,
registers, instructions, initialization and transition function agree literally
with the proved finite machines; no arithmetic opcode is introduced. -/
namespace Holant.Complexity.RationalArithmetic.Execution
open Turing BinaryCompose FixedFieldMachines

abbrev reverse : RawMachine := RawMachine.erase Reverse.machine
abbrev first : RawMachine := RawMachine.erase Wiring.firstMachine
abbrev second : RawMachine := (RawMachine.erase Wiring.swapMachine).compose first
abbrev reversePair : RawMachine := reverse.leftMap.compose reverse.rightMap
abbrev integerAdd : RawMachine := reversePair.compose (RawMachine.erase integerAdditionMachine)
abbrev integerMul : RawMachine := reversePair.compose (RawMachine.erase integerMultiplicationMachine)
abbrev naturalMul : RawMachine := reversePair.compose (RawMachine.erase naturalMultiplicationMachine)
abbrev components : RawMachine :=
  ((RawMachine.erase unpairMachine).compose reverse.leftMap).compose reverse.rightMap
abbrev numerator : RawMachine := components.compose first
abbrev denominator : RawMachine := components.compose second
abbrev packedNormalization : RawMachine :=
  (RawMachine.erase Normalization.machine).compose (RawMachine.erase pairingMachine)
abbrev normalize : RawMachine := reversePair.compose packedNormalization
abbrev leftNumerator : RawMachine := first.compose numerator
abbrev rightNumerator : RawMachine := second.compose numerator
abbrev leftDenominator : RawMachine := first.compose denominator
abbrev rightDenominator : RawMachine := second.compose denominator
abbrev leftDenominatorInteger : RawMachine := leftDenominator.compose (RawMachine.erase natCastMachine)
abbrev rightDenominatorInteger : RawMachine := rightDenominator.compose (RawMachine.erase natCastMachine)
abbrev denominatorProduct : RawMachine := (leftDenominator.pair rightDenominator).compose naturalMul
abbrev numeratorProduct : RawMachine := (leftNumerator.pair rightNumerator).compose integerMul
abbrev leftCrossProduct : RawMachine := (leftNumerator.pair rightDenominatorInteger).compose integerMul
abbrev rightCrossProduct : RawMachine := (rightNumerator.pair leftDenominatorInteger).compose integerMul
abbrev numeratorSum : RawMachine := (leftCrossProduct.pair rightCrossProduct).compose integerAdd
abbrev multiplication : RawMachine := (numeratorProduct.pair denominatorProduct).compose normalize
abbrev addition : RawMachine := (numeratorSum.pair denominatorProduct).compose normalize

end Holant.Complexity.RationalArithmetic.Execution
