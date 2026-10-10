import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentOpposite
import Holant.Complexity.RationalArithmetic.StateChecks

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentOpposite
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev fieldRaw : RawMachine := (RawMachine.erase ParentEndpoint.machine).rightMap
abbrev prepareRaw : RawMachine := fieldRaw.compose (RawMachine.erase OptionContext.machine)
abbrev raw : RawMachine := prepareRaw.compose (RawMachine.erase (OptionMap.machine EdgeSelect.machine))
theorem erase_field : RawMachine.erase fieldMachine=fieldRaw := RawMachine.erase_rightMap _
theorem erase_prepare : RawMachine.erase prepareMachine=prepareRaw := by rw [RawMachine.erase_compose,erase_field]
theorem erase_machine : RawMachine.erase machine=raw := by rw [RawMachine.erase_compose,erase_prepare]
theorem step_eq : HEq raw.view.step machine.computer.step := RawMachine.step_of_erase_eq _ _ erase_machine
theorem start_eq : HEq raw.view.start (initList machine.computer) := RawMachine.start_of_erase_eq _ _ erase_machine
theorem observer_eq :
    letI : Fintype machine.K := machine.finiteK
    letI : DecidableEq machine.K := machine.decidableK
    HEq raw.view.observeHalt (fun c : machine.Config =>
      (c.stk machine.output,decide (∀ k, k ≠ machine.output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_machine

def fieldCheck : RationalArithmetic.StateCheck (RawMachine.erase ParentEndpoint.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def contextCheck : RationalArithmetic.StateCheck (RawMachine.erase OptionContext.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def optionCheck : RationalArithmetic.StateCheck (RawMachine.erase (OptionMap.machine EdgeSelect.machine)) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × (Option Bool × Unit))))
def reset : RationalArithmetic.StateCheck raw := (fieldCheck.rightMap.compose contextCheck).compose optionCheck
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentOpposite
