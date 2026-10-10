import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentRow
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentLabelExecution
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedParentRaw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentQueryWiring
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev secondRaw : RawMachine := (RawMachine.erase Wiring.swapMachine).compose (RawMachine.erase Wiring.firstMachine)
abbrev tableRaw : RawMachine := secondRaw.compose (RawMachine.erase Wiring.firstMachine)
abbrev countRaw : RawMachine := tableRaw.compose (RawMachine.erase Wiring.firstMachine)
abbrev edgeRaw : RawMachine := tableRaw.compose secondRaw
abbrev targetRaw : RawMachine := secondRaw.compose secondRaw
abbrev raw : RawMachine := (RawMachine.erase Wiring.firstMachine).pair
  ((countRaw.pair (RawMachine.erase Wiring.firstMachine)).pair (targetRaw.pair edgeRaw))
theorem erase_second : RawMachine.erase secondMachine=secondRaw := by rw [RawMachine.erase_compose]
theorem erase_table : RawMachine.erase tableMachine=tableRaw := by rw [RawMachine.erase_compose,erase_second]
theorem erase_count : RawMachine.erase countMachine=countRaw := by rw [RawMachine.erase_compose,erase_table]
theorem erase_edge : RawMachine.erase edgeMachine=edgeRaw := by rw [RawMachine.erase_compose,erase_table,erase_second]
theorem erase_target : RawMachine.erase targetMachine=targetRaw := by rw [RawMachine.erase_compose,erase_second]
theorem erase_machine : RawMachine.erase machine=raw := by
  rw [RawMachine.erase_pair,RawMachine.erase_pair,RawMachine.erase_pair,RawMachine.erase_pair,
    erase_count,erase_target,erase_edge]

def secondCheck : RationalArithmetic.StateCheck secondRaw := RationalArithmetic.StateCheck.swap.compose RationalArithmetic.StateCheck.first
def tableCheck : RationalArithmetic.StateCheck tableRaw := secondCheck.compose RationalArithmetic.StateCheck.first
def countCheck : RationalArithmetic.StateCheck countRaw := tableCheck.compose RationalArithmetic.StateCheck.first
def edgeCheck : RationalArithmetic.StateCheck edgeRaw := tableCheck.compose secondCheck
def targetCheck : RationalArithmetic.StateCheck targetRaw := secondCheck.compose secondCheck
def reset : RationalArithmetic.StateCheck raw := RationalArithmetic.StateCheck.first.pair
  ((countCheck.pair RationalArithmetic.StateCheck.first).pair (targetCheck.pair edgeCheck))
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentQueryWiring

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentRow
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev dataRaw : RawMachine := RawComponentLabel.raw.pair RawEdgeTable.raw.leftMap
abbrev prepareRaw : RawMachine := dataRaw.compose ParentQueryWiring.raw
abbrev raw : RawMachine := prepareRaw.compose RootedParent.raw.rightMap

theorem erase_data : RawMachine.erase dataMachine=dataRaw := by
  rw [RawMachine.erase_pair,RawComponentLabel.erase_machine,RawMachine.erase_leftMap,RawEdgeTable.erase_machine]
theorem erase_prepare : RawMachine.erase prepareMachine=prepareRaw := by rw [RawMachine.erase_compose,erase_data,ParentQueryWiring.erase_machine]
theorem erase_machine : RawMachine.erase machine=raw := by rw [RawMachine.erase_compose,erase_prepare,RawMachine.erase_rightMap,RootedParent.erase_machine]
theorem step_eq : HEq raw.view.step machine.computer.step := RawMachine.step_of_erase_eq _ _ erase_machine
theorem start_eq : HEq raw.view.start (initList machine.computer) := RawMachine.start_of_erase_eq _ _ erase_machine
theorem observer_eq :
    letI : Fintype machine.K := machine.finiteK
    letI : DecidableEq machine.K := machine.decidableK
    HEq raw.view.observeHalt (fun c : machine.Config =>
      (c.stk machine.output,decide (∀ k, k ≠ machine.output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_machine

def reset : RationalArithmetic.StateCheck raw :=
  ((RawComponentLabel.reset.pair RawEdgeTable.reset.leftMap).compose ParentQueryWiring.reset).compose RootedParent.reset.rightMap
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentRow
