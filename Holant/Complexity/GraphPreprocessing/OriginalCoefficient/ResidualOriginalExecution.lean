import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalCoefficient
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredExecution
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroCoefficientRaw
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildExecution
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawChildrenExecution

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalCoefficient
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ)
abbrev edgeRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose ParentCoefficient.secondRaw
abbrev prepareRaw : RawMachine := (ActionChild.queryRaw.compose ((RawMachine.erase identityMachine).pair RawParentRow.raw)).pair edgeRaw
abbrev parentRaw : RawMachine := prepareRaw.compose (ResidualStoredCoefficient.raw false a z s b arity)
abbrev zeroRaw : RawMachine := ChildInputWiring.raw.compose (ResidualZeroCoefficient.raw s b arity a z)
theorem erase_edge : RawMachine.erase ResidualContext.edgeMachine=edgeRaw := by rw [RawMachine.erase_compose,ParentCoefficient.erase_second]
theorem erase_prepare : RawMachine.erase prepareMachine=prepareRaw := by
  rw [RawMachine.erase_pair,RawMachine.erase_compose,ActionChild.erase_query,RawMachine.erase_pair,RawParentRow.erase_machine,erase_edge]
theorem erase_parent : RawMachine.erase (parentMachine a z s b arity)=parentRaw a z s b arity := by
  rw [RawMachine.erase_compose,erase_prepare,ResidualStoredCoefficient.erase_machine]
theorem erase_zero : RawMachine.erase (zeroMachine a z s b arity)=zeroRaw a z s b arity := by
  rw [RawMachine.erase_compose,ChildInputWiring.erase_machine,ResidualZeroCoefficient.erase_machine]
theorem parent_step_eq : HEq (parentRaw a z s b arity).view.step (parentMachine a z s b arity).computer.step := RawMachine.step_of_erase_eq _ _ (erase_parent a z s b arity)
theorem parent_start_eq : HEq (parentRaw a z s b arity).view.start (initList (parentMachine a z s b arity).computer) := RawMachine.start_of_erase_eq _ _ (erase_parent a z s b arity)
theorem parent_observer_eq :
    letI : Fintype (parentMachine a z s b arity).K := (parentMachine a z s b arity).finiteK
    letI : DecidableEq (parentMachine a z s b arity).K := (parentMachine a z s b arity).decidableK
    HEq (parentRaw a z s b arity).view.observeHalt (fun c : (parentMachine a z s b arity).Config =>
      (c.stk (parentMachine a z s b arity).output,decide (∀ k, k ≠ (parentMachine a z s b arity).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_parent a z s b arity)
theorem zero_step_eq : HEq (zeroRaw a z s b arity).view.step (zeroMachine a z s b arity).computer.step := RawMachine.step_of_erase_eq _ _ (erase_zero a z s b arity)
theorem zero_start_eq : HEq (zeroRaw a z s b arity).view.start (initList (zeroMachine a z s b arity).computer) := RawMachine.start_of_erase_eq _ _ (erase_zero a z s b arity)
theorem zero_observer_eq :
    letI : Fintype (zeroMachine a z s b arity).K := (zeroMachine a z s b arity).finiteK
    letI : DecidableEq (zeroMachine a z s b arity).K := (zeroMachine a z s b arity).decidableK
    HEq (zeroRaw a z s b arity).view.observeHalt (fun c : (zeroMachine a z s b arity).Config =>
      (c.stk (zeroMachine a z s b arity).output,decide (∀ k, k ≠ (zeroMachine a z s b arity).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_zero a z s b arity)
def prepareCheck : RationalArithmetic.StateCheck prepareRaw :=
  (ActionChild.queryCheck.compose ((@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq Unit))).pair RawParentRow.reset)).pair
    (RationalArithmetic.StateCheck.first.compose ParentCoefficient.secondCheck)
def parentReset : RationalArithmetic.StateCheck (parentRaw a z s b arity) := prepareCheck.compose (ResidualStoredCoefficient.reset false a z s b arity)
def zeroReset : RationalArithmetic.StateCheck (zeroRaw a z s b arity) := ChildInputWiring.reset.compose (ResidualZeroCoefficient.reset s b arity a z)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalCoefficient
