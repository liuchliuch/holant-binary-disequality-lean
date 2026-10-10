import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildLinear
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildExecution

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildLinear
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (s b : ℕ) (arity : ℕ → ℕ)
abbrev renderRaw : RawMachine := (((RawMachine.erase identityMachine).pair (RawMachine.erase (Constant.machine []))).compose
  (RawMachine.erase (OrdinaryCoefficient.prefixMachine [true]))).compose (RawMachine.erase LiteralBits.machine)
abbrev portRaw : RawMachine := (ActionChild.prepareRaw.compose (ParentCoefficient.raw true s b arity)).compose renderRaw
abbrev raw : RawMachine := ((portRaw s b arity).pair (OrdinaryCoefficient.secondRaw.compose ActionChild.referenceRaw)).compose (RawMachine.erase WordJoin.machine)
theorem erase_render : RawMachine.erase renderMachine=renderRaw := by rw [RawMachine.erase_compose,RawMachine.erase_compose,RawMachine.erase_pair]
theorem erase_port : RawMachine.erase (portMachine s b arity)=portRaw s b arity := by
  rw [RawMachine.erase_compose,RawMachine.erase_compose,ActionChild.erase_prepare,ParentCoefficient.erase_machine,erase_render]
theorem erase_machine : RawMachine.erase (machine s b arity)=raw s b arity := by
  rw [RawMachine.erase_compose,RawMachine.erase_pair,erase_port,RawMachine.erase_compose,ParentCoefficient.erase_second,ActionChild.erase_reference]
theorem step_eq : HEq (raw s b arity).view.step (machine s b arity).computer.step := RawMachine.step_of_erase_eq _ _ (erase_machine s b arity)
theorem start_eq : HEq (raw s b arity).view.start (initList (machine s b arity).computer) := RawMachine.start_of_erase_eq _ _ (erase_machine s b arity)
theorem observer_eq :
    letI : Fintype (machine s b arity).K := (machine s b arity).finiteK
    letI : DecidableEq (machine s b arity).K := (machine s b arity).decidableK
    HEq (raw s b arity).view.observeHalt (fun c : (machine s b arity).Config =>
      (c.stk (machine s b arity).output,decide (∀ k, k ≠ (machine s b arity).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_machine s b arity)
def renderCheck : RationalArithmetic.StateCheck renderRaw :=
  (((@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq Unit))).pair
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit))))).compose
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit))))).compose
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit))))
def portCheck : RationalArithmetic.StateCheck (portRaw s b arity) :=
  (ActionChild.prepareCheck.compose (ParentCoefficient.reset true s b arity)).compose renderCheck
def reset : RationalArithmetic.StateCheck (raw s b arity) :=
  ((portCheck s b arity).pair (ParentCoefficient.secondCheck.compose ActionChild.referenceCheck)).compose ActionChild.joinCheck
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildLinear
