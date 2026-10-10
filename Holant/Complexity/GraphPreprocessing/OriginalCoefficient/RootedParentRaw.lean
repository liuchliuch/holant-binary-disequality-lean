import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedParent
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCaseRaw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedFlag
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev secondRaw : RawMachine := (RawMachine.erase Wiring.swapMachine).compose (RawMachine.erase Wiring.firstMachine)
abbrev rootRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose secondRaw
abbrev targetRaw : RawMachine := secondRaw.compose (RawMachine.erase Wiring.firstMachine)
abbrev raw : RawMachine := (rootRaw.pair targetRaw).compose (RawMachine.erase WordCompare.machine)
theorem erase_second : RawMachine.erase secondMachine=secondRaw := by rw [RawMachine.erase_compose]
theorem erase_root : RawMachine.erase rootMachine=rootRaw := by rw [RawMachine.erase_compose,erase_second]
theorem erase_target : RawMachine.erase targetMachine=targetRaw := by rw [RawMachine.erase_compose,erase_second]
theorem erase_machine : RawMachine.erase machine=raw := by rw [RawMachine.erase_compose,RawMachine.erase_pair,erase_root,erase_target]

def secondCheck : RationalArithmetic.StateCheck secondRaw := RationalArithmetic.StateCheck.swap.compose RationalArithmetic.StateCheck.first
def rootCheck : RationalArithmetic.StateCheck rootRaw := RationalArithmetic.StateCheck.first.compose secondCheck
def targetCheck : RationalArithmetic.StateCheck targetRaw := secondCheck.compose RationalArithmetic.StateCheck.first
def compareCheck : RationalArithmetic.StateCheck (RawMachine.erase WordCompare.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq WordCompare.Memory))
def reset : RationalArithmetic.StateCheck raw := (rootCheck.pair targetCheck).compose compareCheck
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedFlag

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedParent
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev prepareRaw : RawMachine := RootedFlag.raw.pair (RawMachine.erase identityMachine)
abbrev caseRaw : RawMachine := RootCase.Raw.machine RootedNonroot.raw
abbrev raw : RawMachine := prepareRaw.compose caseRaw

theorem erase_prepare : RawMachine.erase prepareMachine=prepareRaw := by rw [RawMachine.erase_pair,RootedFlag.erase_machine]
theorem erase_case : RawMachine.erase caseMachine=caseRaw := by rw [RootCase.erase_branch,RootedNonroot.erase_machine]
theorem erase_machine : RawMachine.erase machine=raw := by rw [RawMachine.erase_compose,erase_prepare,erase_case]
theorem step_eq : HEq raw.view.step machine.computer.step := RawMachine.step_of_erase_eq _ _ erase_machine
theorem start_eq : HEq raw.view.start (initList machine.computer) := RawMachine.start_of_erase_eq _ _ erase_machine
theorem observer_eq :
    letI : Fintype machine.K := machine.finiteK
    letI : DecidableEq machine.K := machine.decidableK
    HEq raw.view.observeHalt (fun c : machine.Config =>
      (c.stk machine.output,decide (∀ k, k ≠ machine.output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_machine

def identityCheck : RationalArithmetic.StateCheck (RawMachine.erase identityMachine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq Unit))
def reset : RationalArithmetic.StateCheck raw :=
  (RootedFlag.reset.pair identityCheck).compose (RootCase.reset RootedNonroot.reset)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedParent
