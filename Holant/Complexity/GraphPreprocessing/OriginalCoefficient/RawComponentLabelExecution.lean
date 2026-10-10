import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentLabel
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawRootReachExecution

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentLabel
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev raw : RawMachine := RawRootReach.raw.compose (RawMachine.erase FirstTrue.machine)
theorem erase_machine : RawMachine.erase machine=raw := by
  rw [RawMachine.erase_compose,RawRootReach.erase_machine]
theorem step_eq : HEq raw.view.step machine.computer.step := RawMachine.step_of_erase_eq _ _ erase_machine
theorem start_eq : HEq raw.view.start (initList machine.computer) := RawMachine.start_of_erase_eq _ _ erase_machine
theorem observer_eq :
    letI : Fintype machine.K := machine.finiteK
    letI : DecidableEq machine.K := machine.decidableK
    HEq raw.view.observeHalt (fun c : machine.Config =>
      (c.stk machine.output,decide (∀ k, k ≠ machine.output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_machine

def firstCheck : RationalArithmetic.StateCheck (RawMachine.erase FirstTrue.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def reset : RationalArithmetic.StateCheck raw := RawRootReach.reset.compose firstCheck
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentLabel
