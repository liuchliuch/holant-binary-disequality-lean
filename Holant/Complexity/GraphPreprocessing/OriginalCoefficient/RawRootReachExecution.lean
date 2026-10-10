import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawRootReach
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawEdgeTableExecution
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootReachRaw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootReachWiring
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev secondRaw : RawMachine := (RawMachine.erase Wiring.swapMachine).compose (RawMachine.erase Wiring.firstMachine)
abbrev countRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose (RawMachine.erase Wiring.firstMachine)
abbrev edgesRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose secondRaw
abbrev raw : RawMachine := (countRaw.pair secondRaw).pair edgesRaw

theorem erase_second : RawMachine.erase secondMachine=secondRaw := by rw [RawMachine.erase_compose]
theorem erase_count : RawMachine.erase countMachine=countRaw := by rw [RawMachine.erase_compose]
theorem erase_edges : RawMachine.erase edgesMachine=edgesRaw := by rw [RawMachine.erase_compose,erase_second]
theorem erase_machine : RawMachine.erase machine=raw := by
  rw [RawMachine.erase_pair,RawMachine.erase_pair,erase_count,erase_second,erase_edges]

def secondCheck : RationalArithmetic.StateCheck secondRaw := RationalArithmetic.StateCheck.swap.compose RationalArithmetic.StateCheck.first
def countCheck : RationalArithmetic.StateCheck countRaw := RationalArithmetic.StateCheck.first.compose RationalArithmetic.StateCheck.first
def edgesCheck : RationalArithmetic.StateCheck edgesRaw := RationalArithmetic.StateCheck.first.compose secondCheck
def reset : RationalArithmetic.StateCheck raw := (countCheck.pair secondCheck).pair edgesCheck
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootReachWiring

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawRootReach
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev prepareRaw : RawMachine := RawEdgeTable.raw.leftMap.compose RootReachWiring.raw
abbrev raw : RawMachine := prepareRaw.compose RootReach.raw

theorem erase_prepare : RawMachine.erase prepareMachine=prepareRaw := by
  rw [RawMachine.erase_compose,RawMachine.erase_leftMap,RawEdgeTable.erase_machine,RootReachWiring.erase_machine]
theorem erase_machine : RawMachine.erase machine=raw := by
  rw [RawMachine.erase_compose,erase_prepare,RootReach.erase_machine]

theorem step_eq : HEq raw.view.step machine.computer.step := RawMachine.step_of_erase_eq _ _ erase_machine
theorem start_eq : HEq raw.view.start (initList machine.computer) := RawMachine.start_of_erase_eq _ _ erase_machine
theorem observer_eq :
    letI : Fintype machine.K := machine.finiteK
    letI : DecidableEq machine.K := machine.decidableK
    HEq raw.view.observeHalt (fun c : machine.Config =>
      (c.stk machine.output,decide (∀ k, k ≠ machine.output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_machine

def reset : RationalArithmetic.StateCheck raw :=
  (RawEdgeTable.reset.leftMap.compose RootReachWiring.reset).compose RootReach.reset

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawRootReach
