import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedNonroot
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearchRaw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedNonroot
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev rootRaw : RawMachine := (RawMachine.erase RootBitmap.machine).leftMap
abbrev raw : RawMachine := rootRaw.compose ParentSearch.raw

theorem erase_machine : RawMachine.erase machine=raw := by
  change RawMachine.erase ((LeftMap.machine RootBitmap.machine).compose (ParentSearch.machine ParentSearch.actual)) = _
  rw [RawMachine.erase_compose,RawMachine.erase_leftMap,ParentSearch.erase_actual]

theorem step_eq : HEq raw.view.step machine.computer.step := RawMachine.step_of_erase_eq _ _ erase_machine
theorem start_eq : HEq raw.view.start (initList machine.computer) := RawMachine.start_of_erase_eq _ _ erase_machine
theorem observer_eq :
    letI : Fintype machine.K := machine.finiteK
    letI : DecidableEq machine.K := machine.decidableK
    HEq raw.view.observeHalt (fun c : machine.Config =>
      (c.stk machine.output,decide (∀ k, k ≠ machine.output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_machine

def rootCheck : RationalArithmetic.StateCheck (RawMachine.erase RootBitmap.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def reset : RationalArithmetic.StateCheck raw := rootCheck.leftMap.compose ParentSearch.reset

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedNonroot
