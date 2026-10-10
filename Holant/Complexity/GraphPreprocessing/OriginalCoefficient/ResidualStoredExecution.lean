import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredCoefficient
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParentCoefficientRaw
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficientExecution

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredWiring
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
abbrev rawRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose (RawMachine.erase Wiring.firstMachine)
abbrev tailRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose ParentCoefficient.secondRaw
abbrev vertexRaw : RawMachine := tailRaw.compose (RawMachine.erase Wiring.firstMachine)
abbrev parentRaw : RawMachine := tailRaw.compose ParentCoefficient.secondRaw
abbrev raw : RawMachine := rawRaw.pair (vertexRaw.pair (ParentCoefficient.secondRaw.pair parentRaw))
theorem erase_raw : RawMachine.erase rawMachine=rawRaw := RawMachine.erase_compose _ _
theorem erase_tail : RawMachine.erase tailMachine=tailRaw := by rw [RawMachine.erase_compose,ParentCoefficient.erase_second]
theorem erase_vertex : RawMachine.erase vertexMachine=vertexRaw := by rw [RawMachine.erase_compose,erase_tail]
theorem erase_parent : RawMachine.erase parentMachine=parentRaw := by rw [RawMachine.erase_compose,erase_tail,ParentCoefficient.erase_second]
theorem erase_machine : RawMachine.erase machine=raw := by
  rw [RawMachine.erase_pair,erase_raw,RawMachine.erase_pair,erase_vertex,RawMachine.erase_pair,ParentCoefficient.erase_second,erase_parent]
def tailCheck : RationalArithmetic.StateCheck tailRaw := RationalArithmetic.StateCheck.first.compose ParentCoefficient.secondCheck
def reset : RationalArithmetic.StateCheck raw :=
  (RationalArithmetic.StateCheck.first.compose RationalArithmetic.StateCheck.first).pair
    ((tailCheck.compose RationalArithmetic.StateCheck.first).pair
      (ParentCoefficient.secondCheck.pair (tailCheck.compose ParentCoefficient.secondCheck)))
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredWiring

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredCoefficient
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (flip a z : Bool) (s b : ℕ) (arity : ℕ → ℕ)
abbrev prepareRaw : RawMachine := (ParentCoefficient.prepareRaw flip).leftMap.compose ResidualStoredWiring.raw
abbrev raw : RawMachine := (prepareRaw flip).compose (ResidualParentCoefficient.raw s b arity a z)
theorem erase_prepare : RawMachine.erase (prepareMachine flip)=prepareRaw flip := by
  rw [RawMachine.erase_compose,RawMachine.erase_leftMap,ParentCoefficient.erase_prepare,ResidualStoredWiring.erase_machine]
theorem erase_machine : RawMachine.erase (machine flip a z s b arity)=raw flip a z s b arity := by
  rw [RawMachine.erase_compose,erase_prepare,ResidualParentCoefficient.erase_machine]
theorem step_eq : HEq (raw flip a z s b arity).view.step (machine flip a z s b arity).computer.step := RawMachine.step_of_erase_eq _ _ (erase_machine flip a z s b arity)
theorem start_eq : HEq (raw flip a z s b arity).view.start (initList (machine flip a z s b arity).computer) := RawMachine.start_of_erase_eq _ _ (erase_machine flip a z s b arity)
theorem observer_eq :
    letI : Fintype (machine flip a z s b arity).K := (machine flip a z s b arity).finiteK
    letI : DecidableEq (machine flip a z s b arity).K := (machine flip a z s b arity).decidableK
    HEq (raw flip a z s b arity).view.observeHalt (fun c : (machine flip a z s b arity).Config =>
      (c.stk (machine flip a z s b arity).output,decide (∀ k, k ≠ (machine flip a z s b arity).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_machine flip a z s b arity)
def prepareCheck : RationalArithmetic.StateCheck (prepareRaw flip) :=
  (((ParentCoefficient.rowCheck flip).rightMap.compose ParentCoefficient.wireCheck).leftMap).compose ResidualStoredWiring.reset
def reset : RationalArithmetic.StateCheck (raw flip a z s b arity) := (prepareCheck flip).compose (ResidualParentCoefficient.reset s b arity a z)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredCoefficient
