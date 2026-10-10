import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildMeaning
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildBounds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficientExecution

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (s b : ℕ) (arity : ℕ → ℕ)

abbrev queryRaw : RawMachine := ((RawMachine.erase Wiring.firstMachine).compose (RawMachine.erase Wiring.firstMachine)).pair OrdinaryCoefficient.secondRaw
abbrev prepareRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).pair (queryRaw.compose RawParentRow.raw)
abbrev portRaw : RawMachine := (prepareRaw.compose (ParentCoefficient.raw true s b arity)).compose (RawMachine.erase (portActionMachine s b arity))
abbrev referenceRaw : RawMachine := (((RawMachine.erase identityMachine).pair (RawMachine.erase (Constant.machine [false]))).compose
  (RawMachine.erase WordJoin.machine)).compose (RawMachine.erase (OrdinaryCoefficient.prefixMachine [true]))
abbrev raw : RawMachine := ((portRaw s b arity).pair (OrdinaryCoefficient.secondRaw.compose referenceRaw)).compose (RawMachine.erase WordJoin.machine)

theorem erase_query : RawMachine.erase queryMachine=queryRaw := by
  rw [RawMachine.erase_pair,RawMachine.erase_compose,ParentCoefficient.erase_second]
theorem erase_prepare : RawMachine.erase prepareMachine=prepareRaw := by
  rw [RawMachine.erase_pair,RawMachine.erase_compose,erase_query,RawParentRow.erase_machine]
theorem erase_port : RawMachine.erase (portMachine s b arity)=portRaw s b arity := by
  rw [RawMachine.erase_compose,RawMachine.erase_compose,erase_prepare,ParentCoefficient.erase_machine]
theorem erase_reference : RawMachine.erase referenceMachine=referenceRaw := by
  rw [RawMachine.erase_compose,RawMachine.erase_compose,RawMachine.erase_pair]
theorem erase_machine : RawMachine.erase (machine s b arity)=raw s b arity := by
  rw [RawMachine.erase_compose,RawMachine.erase_pair,erase_port,RawMachine.erase_compose,ParentCoefficient.erase_second,erase_reference]
theorem step_eq : HEq (raw s b arity).view.step (machine s b arity).computer.step := RawMachine.step_of_erase_eq _ _ (erase_machine s b arity)
theorem start_eq : HEq (raw s b arity).view.start (initList (machine s b arity).computer) := RawMachine.start_of_erase_eq _ _ (erase_machine s b arity)
theorem observer_eq :
    letI : Fintype (machine s b arity).K := (machine s b arity).finiteK
    letI : DecidableEq (machine s b arity).K := (machine s b arity).decidableK
    HEq (raw s b arity).view.observeHalt (fun c : (machine s b arity).Config =>
      (c.stk (machine s b arity).output,decide (∀ k, k ≠ (machine s b arity).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_machine s b arity)

def queryCheck : RationalArithmetic.StateCheck queryRaw :=
  (RationalArithmetic.StateCheck.first.compose RationalArithmetic.StateCheck.first).pair ParentCoefficient.secondCheck
def prepareCheck : RationalArithmetic.StateCheck prepareRaw := RationalArithmetic.StateCheck.first.pair (queryCheck.compose RawParentRow.reset)
def portCheck : RationalArithmetic.StateCheck (portRaw s b arity) :=
  (prepareCheck.compose (ParentCoefficient.reset true s b arity)).compose
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit))))
def joinCheck : RationalArithmetic.StateCheck (RawMachine.erase WordJoin.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def referenceCheck : RationalArithmetic.StateCheck referenceRaw :=
  (((@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq Unit))).pair
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit))))).compose joinCheck).compose
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit))))
def reset : RationalArithmetic.StateCheck (raw s b arity) :=
  ((portCheck s b arity).pair (ParentCoefficient.secondCheck.compose referenceCheck)).compose joinCheck
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild
