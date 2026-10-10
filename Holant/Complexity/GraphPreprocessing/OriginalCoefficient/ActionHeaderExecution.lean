import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeader
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficientExecution

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeader
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (s b : ℕ) (arity : ℕ → ℕ)

abbrev presenceRaw : RawMachine := ((RawMachine.erase ParentEndpoint.machine).compose
  (RawMachine.erase (OptionMap.machine (Constant.machine [true])))).compose (RawMachine.erase OptionAny.machine)
abbrev flagRaw : RawMachine := OrdinaryCoefficient.secondRaw.compose presenceRaw
abbrev zeroRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose (OrdinaryCoefficient.zeroRaw s b arity)
abbrev dataRaw : RawMachine := flagRaw.pair ((zeroRaw s b arity).pair (ParentCoefficient.raw false s b arity))
abbrev emitRaw : RawMachine := (RawMachine.erase HeaderWords.machine).compose (RawMachine.erase LiteralBits.machine)
abbrev raw : RawMachine := (dataRaw s b arity).compose emitRaw
theorem erase_presence : RawMachine.erase presenceMachine=presenceRaw := by rw [RawMachine.erase_compose,RawMachine.erase_compose]
theorem erase_flag : RawMachine.erase flagMachine=flagRaw := by rw [RawMachine.erase_compose,ParentCoefficient.erase_second,erase_presence]
theorem erase_zero : RawMachine.erase (zeroMachine s b arity)=zeroRaw s b arity := by rw [RawMachine.erase_compose,OrdinaryCoefficient.erase_zero]
theorem erase_data : RawMachine.erase (dataMachine s b arity)=dataRaw s b arity := by
  rw [RawMachine.erase_pair,erase_flag,RawMachine.erase_pair,erase_zero,ParentCoefficient.erase_machine]
theorem erase_emit : RawMachine.erase (emitMachine s b arity)=emitRaw := RawMachine.erase_compose _ _
theorem erase_machine : RawMachine.erase (machine s b arity)=raw s b arity := by rw [RawMachine.erase_compose,erase_data,erase_emit]
theorem step_eq : HEq (raw s b arity).view.step (machine s b arity).computer.step := RawMachine.step_of_erase_eq _ _ (erase_machine s b arity)
theorem start_eq : HEq (raw s b arity).view.start (initList (machine s b arity).computer) := RawMachine.start_of_erase_eq _ _ (erase_machine s b arity)
theorem observer_eq :
    letI : Fintype (machine s b arity).K := (machine s b arity).finiteK
    letI : DecidableEq (machine s b arity).K := (machine s b arity).decidableK
    HEq (raw s b arity).view.observeHalt (fun c : (machine s b arity).Config =>
      (c.stk (machine s b arity).output,decide (∀ k, k ≠ (machine s b arity).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_machine s b arity)

def presenceCheck : RationalArithmetic.StateCheck presenceRaw :=
  ((@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))).compose
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × (Option Bool × Unit)))))).compose
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit))))
def flagCheck : RationalArithmetic.StateCheck flagRaw := ParentCoefficient.secondCheck.compose presenceCheck
def zeroCheck : RationalArithmetic.StateCheck (zeroRaw s b arity) := RationalArithmetic.StateCheck.first.compose (OrdinaryCoefficient.zeroReset s b arity)
def emitCheck : RationalArithmetic.StateCheck emitRaw :=
  (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))).compose
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit))))
def reset : RationalArithmetic.StateCheck (raw s b arity) :=
  (flagCheck.pair ((zeroCheck s b arity).pair (ParentCoefficient.reset false s b arity))).compose emitCheck
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeader
