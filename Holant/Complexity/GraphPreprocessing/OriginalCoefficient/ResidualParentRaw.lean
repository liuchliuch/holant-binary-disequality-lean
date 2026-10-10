import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParentBounds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonRaw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParent
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 400000
set_option Elab.async false

abbrev cutRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).rightMap.rightMap
abbrev survivorRaw : RawMachine := ((RawMachine.erase Wiring.swapMachine).compose
  (RawMachine.erase Wiring.firstMachine)).rightMap.rightMap
abbrev pinRaw (side value : Bool) : RawMachine := cutRaw.compose (RawMachine.erase (ResidualPinQuery.machine side value))
abbrev portRaw : RawMachine := survivorRaw.compose (RawMachine.erase ResidualOptionalSurvivor.machine)
def raw (a z : Bool) : RawMachine := (pinRaw false a).pair ((pinRaw true z).pair portRaw)

theorem erase_cut : RawMachine.erase cutMachine = cutRaw := ResidualSingleton.erase_cut
theorem erase_survivor : RawMachine.erase survivorMachine = survivorRaw := ResidualSingleton.erase_survivor
theorem erase_pin (side value : Bool) :
    RawMachine.erase (cutMachine.compose (ResidualPinQuery.machine side value)) = pinRaw side value :=
  (RawMachine.erase_compose _ _).trans
    (congrArg (fun m => m.compose (RawMachine.erase (ResidualPinQuery.machine side value))) erase_cut)
theorem erase_port :
    RawMachine.erase (survivorMachine.compose ResidualOptionalSurvivor.machine) = portRaw :=
  (RawMachine.erase_compose _ _).trans
    (congrArg (fun m => m.compose (RawMachine.erase ResidualOptionalSurvivor.machine)) erase_survivor)

theorem erase_machine (a z : Bool) : RawMachine.erase (machine a z) = raw a z := by
  change RawMachine.erase (pairMachine _ (pairMachine _ _)) = _
  rw [RawMachine.erase_pair,RawMachine.erase_pair,erase_pin,erase_pin,erase_port]
  rfl

theorem step_eq (a z : Bool) : HEq (raw a z).view.step (machine a z).computer.step :=
  RawMachine.step_of_erase_eq _ _ (erase_machine a z)
theorem start_eq (a z : Bool) : HEq (raw a z).view.start (initList (machine a z).computer) :=
  RawMachine.start_of_erase_eq _ _ (erase_machine a z)
theorem observer_eq (a z : Bool) :
    letI : Fintype (machine a z).K := (machine a z).finiteK
    letI : DecidableEq (machine a z).K := (machine a z).decidableK
    HEq (raw a z).view.observeHalt
      (fun c : (machine a z).Config => (c.stk (machine a z).output,
        decide (∀ k, k ≠ (machine a z).output → c.stk k = []))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_machine a z)

def cutCheck : RationalArithmetic.StateCheck cutRaw :=
  RationalArithmetic.StateCheck.first.rightMap.rightMap

def survivorCheck : RationalArithmetic.StateCheck survivorRaw :=
  (RationalArithmetic.StateCheck.swap.compose RationalArithmetic.StateCheck.first).rightMap.rightMap

def portCheck : RationalArithmetic.StateCheck (RawMachine.erase ResidualOptionalSurvivor.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (WordEqual.Memory Unit)))

def reset (a z : Bool) : RationalArithmetic.StateCheck (raw a z) :=
  (cutCheck.compose (ResidualZeroDescriptor.pinCheck false a)).pair
    ((cutCheck.compose (ResidualZeroDescriptor.pinCheck true z)).pair (survivorCheck.compose portCheck))

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParent
