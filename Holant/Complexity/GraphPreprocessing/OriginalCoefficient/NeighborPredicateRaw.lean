import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicateSpec
import Holant.Complexity.RationalArithmetic.StateChecks

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicate
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev comparisonRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose (RawMachine.erase WordCompare.machine)
abbrev membershipRaw : RawMachine :=
  ((RawMachine.erase Wiring.swapMachine).compose (RawMachine.erase Wiring.firstMachine)).compose (RawMachine.erase BitRead.machine)
abbrev raw : RawMachine := (comparisonRaw.pair membershipRaw).compose (RawMachine.erase andMachine)

theorem erase_machine : RawMachine.erase machine = raw := by
  change RawMachine.erase ((pairMachine comparisonMachine membershipMachine).compose andMachine) = _
  rw [RawMachine.erase_compose,RawMachine.erase_pair]
  simp only [comparisonMachine,membershipMachine,secondMachine,RawMachine.erase_compose]

theorem step_eq : HEq raw.view.step machine.computer.step := RawMachine.step_of_erase_eq _ _ erase_machine
theorem start_eq : HEq raw.view.start (initList machine.computer) := RawMachine.start_of_erase_eq _ _ erase_machine
theorem observer_eq :
    letI : Fintype machine.K := machine.finiteK
    letI : DecidableEq machine.K := machine.decidableK
    HEq raw.view.observeHalt (fun c : machine.Config =>
      (c.stk machine.output,decide (∀ k, k ≠ machine.output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_machine

def comparisonCheck : RationalArithmetic.StateCheck comparisonRaw :=
  RationalArithmetic.StateCheck.first.compose
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq WordCompare.Memory)))
def membershipCheck : RationalArithmetic.StateCheck membershipRaw :=
  (RationalArithmetic.StateCheck.swap.compose RationalArithmetic.StateCheck.first).compose
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit))))
def andCheck : RationalArithmetic.StateCheck (RawMachine.erase andMachine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def reset : RationalArithmetic.StateCheck raw := (comparisonCheck.pair membershipCheck).compose andCheck

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicate
