import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficient
import Holant.Complexity.RationalArithmetic.StateChecks

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficient
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (s b : ℕ) (arity : ℕ → ℕ)

abbrev secondRaw : RawMachine := (RawMachine.erase Wiring.swapMachine).compose (RawMachine.erase Wiring.firstMachine)
abbrev contextRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).pair (secondRaw.compose (RawMachine.erase Wiring.firstMachine))
abbrev raw : RawMachine := (contextRaw.pair
  ((RawMachine.erase ResidualOptionalSurvivor.machine).compose (RawMachine.erase (prefixMachine absentPins)))).compose
  (RawMachine.erase (VertexDescriptor.machine s b arity))
abbrev zeroRaw : RawMachine := ((RawMachine.erase identityMachine).pair
  (RawMachine.erase (Constant.machine (absentPins++[false])))).compose (RawMachine.erase (VertexDescriptor.machine s b arity))

theorem erase_context : RawMachine.erase contextMachine=contextRaw := by
  rw [RawMachine.erase_pair,RawMachine.erase_compose,RawMachine.erase_compose]
theorem erase_machine : RawMachine.erase (machine s b arity)=raw s b arity := by
  rw [RawMachine.erase_compose,RawMachine.erase_pair,erase_context,RawMachine.erase_compose]
theorem erase_zero : RawMachine.erase (zeroMachine s b arity)=zeroRaw s b arity := by
  rw [RawMachine.erase_compose,RawMachine.erase_pair]
theorem step_eq : HEq (raw s b arity).view.step (machine s b arity).computer.step := RawMachine.step_of_erase_eq _ _ (erase_machine s b arity)
theorem start_eq : HEq (raw s b arity).view.start (initList (machine s b arity).computer) := RawMachine.start_of_erase_eq _ _ (erase_machine s b arity)
theorem observer_eq :
    letI : Fintype (machine s b arity).K := (machine s b arity).finiteK
    letI : DecidableEq (machine s b arity).K := (machine s b arity).decidableK
    HEq (raw s b arity).view.observeHalt (fun c : (machine s b arity).Config =>
      (c.stk (machine s b arity).output,decide (∀ k, k ≠ (machine s b arity).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_machine s b arity)
theorem zero_step_eq : HEq (zeroRaw s b arity).view.step (zeroMachine s b arity).computer.step := RawMachine.step_of_erase_eq _ _ (erase_zero s b arity)
theorem zero_start_eq : HEq (zeroRaw s b arity).view.start (initList (zeroMachine s b arity).computer) := RawMachine.start_of_erase_eq _ _ (erase_zero s b arity)
theorem zero_observer_eq :
    letI : Fintype (zeroMachine s b arity).K := (zeroMachine s b arity).finiteK
    letI : DecidableEq (zeroMachine s b arity).K := (zeroMachine s b arity).decidableK
    HEq (zeroRaw s b arity).view.observeHalt (fun c : (zeroMachine s b arity).Config =>
      (c.stk (zeroMachine s b arity).output,decide (∀ k, k ≠ (zeroMachine s b arity).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_zero s b arity)

def descriptorCheck : RationalArithmetic.StateCheck (RawMachine.erase (VertexDescriptor.machine s b arity)) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def optionalCheck : RationalArithmetic.StateCheck (RawMachine.erase ResidualOptionalSurvivor.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (WordEqual.Memory Unit)))
def prefixCheck : RationalArithmetic.StateCheck (RawMachine.erase (prefixMachine absentPins)) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def contextCheck : RationalArithmetic.StateCheck contextRaw :=
  RationalArithmetic.StateCheck.first.pair ((RationalArithmetic.StateCheck.swap.compose RationalArithmetic.StateCheck.first).compose RationalArithmetic.StateCheck.first)
def reset : RationalArithmetic.StateCheck (raw s b arity) :=
  (contextCheck.pair (optionalCheck.compose prefixCheck)).compose (descriptorCheck s b arity)
def zeroReset : RationalArithmetic.StateCheck (zeroRaw s b arity) :=
  ((@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq Unit))).pair
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit))))).compose (descriptorCheck s b arity)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficient
