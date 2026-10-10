import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawChildren
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentTableExecution
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateRaw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildInputWiring
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
abbrev secondRaw : RawMachine := (RawMachine.erase Wiring.swapMachine).compose (RawMachine.erase Wiring.firstMachine)
abbrev edgesRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose (RawMachine.erase Wiring.firstMachine)
abbrev rowsRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose secondRaw
abbrev raw : RawMachine := edgesRaw.pair (secondRaw.pair rowsRaw)
theorem erase_second : RawMachine.erase secondMachine=secondRaw := by rw [RawMachine.erase_compose]
theorem erase_edges : RawMachine.erase edgesMachine=edgesRaw := by rw [RawMachine.erase_compose]
theorem erase_rows : RawMachine.erase rowsMachine=rowsRaw := by rw [RawMachine.erase_compose,erase_second]
theorem erase_machine : RawMachine.erase machine=raw := by
  rw [RawMachine.erase_pair,RawMachine.erase_pair,erase_edges,erase_second,erase_rows]
def secondCheck : RationalArithmetic.StateCheck secondRaw := RationalArithmetic.StateCheck.swap.compose RationalArithmetic.StateCheck.first
def edgesCheck : RationalArithmetic.StateCheck edgesRaw := RationalArithmetic.StateCheck.first.compose RationalArithmetic.StateCheck.first
def rowsCheck : RationalArithmetic.StateCheck rowsRaw := RationalArithmetic.StateCheck.first.compose secondCheck
def reset : RationalArithmetic.StateCheck raw := edgesCheck.pair (secondCheck.pair rowsCheck)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildInputWiring

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawChildren
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
abbrev edgesRaw : RawMachine := RawEdgeTable.raw.compose ChildInputWiring.secondRaw
abbrev contextRaw : RawMachine := edgesRaw.pair RawParentTable.raw
abbrev prepareRaw : RawMachine := contextRaw.leftMap.compose ChildInputWiring.raw
abbrev raw : RawMachine := prepareRaw.compose ChildEnumerate.raw
theorem erase_edges : RawMachine.erase edgesMachine=edgesRaw := by
  rw [RawMachine.erase_compose,RawEdgeTable.erase_machine,ChildInputWiring.erase_second]
theorem erase_context : RawMachine.erase contextMachine=contextRaw := by
  rw [RawMachine.erase_pair,erase_edges,RawParentTable.erase_machine]
theorem erase_prepare : RawMachine.erase prepareMachine=prepareRaw := by
  rw [RawMachine.erase_compose,RawMachine.erase_leftMap,erase_context,ChildInputWiring.erase_machine]
theorem erase_machine : RawMachine.erase machine=raw := by
  rw [RawMachine.erase_compose,erase_prepare,ChildEnumerate.erase_actual]
theorem step_eq : HEq raw.view.step machine.computer.step := RawMachine.step_of_erase_eq _ _ erase_machine
theorem start_eq : HEq raw.view.start (initList machine.computer) := RawMachine.start_of_erase_eq _ _ erase_machine
theorem observer_eq :
    letI : Fintype machine.K := machine.finiteK
    letI : DecidableEq machine.K := machine.decidableK
    HEq raw.view.observeHalt (fun c : machine.Config =>
      (c.stk machine.output,decide (∀ k, k ≠ machine.output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_machine

def edgesCheck : RationalArithmetic.StateCheck edgesRaw := RawEdgeTable.reset.compose ChildInputWiring.secondCheck
def contextCheck : RationalArithmetic.StateCheck contextRaw := edgesCheck.pair RawParentTable.reset
def reset : RationalArithmetic.StateCheck raw := (contextCheck.leftMap.compose ChildInputWiring.reset).compose ChildEnumerate.reset
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawChildren
