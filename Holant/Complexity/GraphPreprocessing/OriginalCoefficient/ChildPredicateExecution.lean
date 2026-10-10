import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildPredicate
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentOppositeExecution

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildPredicate
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev prepareRaw : RawMachine := ParentOpposite.raw.rightMap.compose (RawMachine.erase OptionContext.machine)
abbrev raw : RawMachine := (prepareRaw.compose (RawMachine.erase (OptionMap.machine WordCompare.machine))).compose (RawMachine.erase OptionAny.machine)
theorem erase_prepare : RawMachine.erase prepareMachine=prepareRaw := by rw [RawMachine.erase_compose,RawMachine.erase_rightMap,ParentOpposite.erase_machine]
theorem erase_machine : RawMachine.erase machine=raw := by rw [RawMachine.erase_compose,RawMachine.erase_compose,erase_prepare]
theorem step_eq : HEq raw.view.step machine.computer.step := RawMachine.step_of_erase_eq _ _ erase_machine
theorem start_eq : HEq raw.view.start (initList machine.computer) := RawMachine.start_of_erase_eq _ _ erase_machine
theorem observer_eq :
    letI : Fintype machine.K := machine.finiteK
    letI : DecidableEq machine.K := machine.decidableK
    HEq raw.view.observeHalt (fun c : machine.Config =>
      (c.stk machine.output,decide (∀ k, k ≠ machine.output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_machine

def compareCheck : RationalArithmetic.StateCheck (RawMachine.erase (OptionMap.machine WordCompare.machine)) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × WordCompare.Memory)))
def collapseCheck : RationalArithmetic.StateCheck (RawMachine.erase OptionAny.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def reset : RationalArithmetic.StateCheck raw :=
  ((ParentOpposite.reset.rightMap.compose ParentOpposite.contextCheck).compose compareCheck).compose collapseCheck
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildPredicate
