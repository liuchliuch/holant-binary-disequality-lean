import Holant.Complexity.RationalArithmetic.Operations
import Holant.Complexity.FixedFieldMachines.MachineSyntax

/-! Executable views of the concrete scalar machines, separate from polynomial
proof packages. These are fixed finite syntax trees assembled before input is
read; all words are manipulated only by the compiled TM2 statements. -/
namespace Holant.Complexity.RationalArithmetic.Syntax
open BinaryCompose FixedFieldMachines

abbrev reversePair : Machine :=
  (LeftMap.machine Reverse.machine).compose (rightMapMachine Reverse.machine)
abbrev integerAdd : Machine := reversePair.compose integerAdditionMachine
abbrev integerMul : Machine := reversePair.compose integerMultiplicationMachine
abbrev naturalMul : Machine := reversePair.compose naturalMultiplicationMachine
abbrev components : Machine :=
  (unpairMachine.compose (LeftMap.machine Reverse.machine)).compose (rightMapMachine Reverse.machine)
abbrev numerator : Machine := components.compose Wiring.firstMachine
abbrev denominator : Machine := components.compose secondMachine
abbrev normalize : Machine := reversePair.compose normalizationMachine
abbrev leftNumerator : Machine := Wiring.firstMachine.compose numerator
abbrev rightNumerator : Machine := secondMachine.compose numerator
abbrev leftDenominator : Machine := Wiring.firstMachine.compose denominator
abbrev rightDenominator : Machine := secondMachine.compose denominator
abbrev leftDenominatorInteger : Machine := leftDenominator.compose natCastMachine
abbrev rightDenominatorInteger : Machine := rightDenominator.compose natCastMachine
abbrev denominatorProduct : Machine := (pairMachine leftDenominator rightDenominator).compose naturalMul
abbrev numeratorProduct : Machine := (pairMachine leftNumerator rightNumerator).compose integerMul
abbrev leftCrossProduct : Machine := (pairMachine leftNumerator rightDenominatorInteger).compose integerMul
abbrev rightCrossProduct : Machine := (pairMachine rightNumerator leftDenominatorInteger).compose integerMul
abbrev numeratorSum : Machine := (pairMachine leftCrossProduct rightCrossProduct).compose integerAdd
abbrev multiplication : Machine := (pairMachine numeratorProduct denominatorProduct).compose normalize
abbrev addition : Machine := (pairMachine numeratorSum denominatorProduct).compose normalize

@[simp] theorem multiplication_machine : multiplicationComputes.machine = multiplication := rfl
@[simp] theorem addition_machine : additionComputes.machine = addition := rfl
@[simp] theorem components_machine : componentsComputes.machine = components := rfl
@[simp] theorem normalizationForward_machine : normalizationForwardComputes.machine = normalize := rfl


end Holant.Complexity.RationalArithmetic.Syntax
