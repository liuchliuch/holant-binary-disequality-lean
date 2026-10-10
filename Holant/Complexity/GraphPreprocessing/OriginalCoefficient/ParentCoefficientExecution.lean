import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficientBounds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficientExecution
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentRowExecution

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficient
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (flip : Bool) (s b : ℕ) (arity : ℕ → ℕ)

abbrev rowRaw : RawMachine := (RawMachine.erase ParentEndpoint.machine).compose
  (RawMachine.erase (OptionMap.machine (endpointMachine flip)))
abbrev secondRaw : RawMachine := OrdinaryCoefficient.secondRaw
abbrev rawWireRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose (RawMachine.erase Wiring.firstMachine)
abbrev vertexWireRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).compose secondRaw
abbrev wireRaw : RawMachine := rawWireRaw.pair (vertexWireRaw.pair secondRaw)
abbrev prepareRaw : RawMachine := (rowRaw flip).rightMap.compose wireRaw
abbrev raw : RawMachine := (prepareRaw flip).compose (OrdinaryCoefficient.raw s b arity)
abbrev originalRaw : RawMachine := ((RawMachine.erase identityMachine).pair RawParentRow.raw).compose (raw false s b arity)

theorem erase_row : RawMachine.erase (rowMachine flip)=rowRaw flip := RawMachine.erase_compose _ _
theorem erase_second : RawMachine.erase secondMachine=secondRaw := by rw [RawMachine.erase_compose]
theorem erase_rawWire : RawMachine.erase rawWireMachine=rawWireRaw := RawMachine.erase_compose _ _
theorem erase_vertexWire : RawMachine.erase vertexWireMachine=vertexWireRaw := by rw [RawMachine.erase_compose,erase_second]
theorem erase_wire : RawMachine.erase wireMachine=wireRaw := by
  rw [RawMachine.erase_pair,erase_rawWire,RawMachine.erase_pair,erase_vertexWire,erase_second]
theorem erase_prepare : RawMachine.erase (prepareMachine flip)=prepareRaw flip := by
  rw [RawMachine.erase_compose,RawMachine.erase_rightMap,erase_row,erase_wire]
theorem erase_machine : RawMachine.erase (machine flip s b arity)=raw flip s b arity := by
  rw [RawMachine.erase_compose,erase_prepare,OrdinaryCoefficient.erase_machine]
theorem erase_original : RawMachine.erase (originalMachine s b arity)=originalRaw s b arity := by
  rw [RawMachine.erase_compose,RawMachine.erase_pair,RawParentRow.erase_machine,erase_machine]
theorem step_eq : HEq (raw flip s b arity).view.step (machine flip s b arity).computer.step := RawMachine.step_of_erase_eq _ _ (erase_machine flip s b arity)
theorem start_eq : HEq (raw flip s b arity).view.start (initList (machine flip s b arity).computer) := RawMachine.start_of_erase_eq _ _ (erase_machine flip s b arity)
theorem observer_eq :
    letI : Fintype (machine flip s b arity).K := (machine flip s b arity).finiteK
    letI : DecidableEq (machine flip s b arity).K := (machine flip s b arity).decidableK
    HEq (raw flip s b arity).view.observeHalt (fun c : (machine flip s b arity).Config =>
      (c.stk (machine flip s b arity).output,decide (∀ k, k ≠ (machine flip s b arity).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_machine flip s b arity)
theorem original_step_eq : HEq (originalRaw s b arity).view.step (originalMachine s b arity).computer.step := RawMachine.step_of_erase_eq _ _ (erase_original s b arity)
theorem original_start_eq : HEq (originalRaw s b arity).view.start (initList (originalMachine s b arity).computer) := RawMachine.start_of_erase_eq _ _ (erase_original s b arity)
theorem original_observer_eq :
    letI : Fintype (originalMachine s b arity).K := (originalMachine s b arity).finiteK
    letI : DecidableEq (originalMachine s b arity).K := (originalMachine s b arity).decidableK
    HEq (originalRaw s b arity).view.observeHalt (fun c : (originalMachine s b arity).Config =>
      (c.stk (originalMachine s b arity).output,decide (∀ k, k ≠ (originalMachine s b arity).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_original s b arity)

def endpointCheck : RationalArithmetic.StateCheck (RawMachine.erase (OptionMap.machine (endpointMachine flip))) :=
  @RationalArithmetic.StateCheck.ofEq _ (by
    dsimp [RawMachine.erase,OptionMap.machine,endpointMachine,Machine.compose,EndpointQuery.machine,LeftMap.machine,rightMapMachine,sideMachine,FiniteRecode.machine]
    infer_instance)
def rowCheck : RationalArithmetic.StateCheck (rowRaw flip) :=
  (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))).compose (endpointCheck flip)
def secondCheck : RationalArithmetic.StateCheck secondRaw := RationalArithmetic.StateCheck.swap.compose RationalArithmetic.StateCheck.first
def wireCheck : RationalArithmetic.StateCheck wireRaw :=
  (RationalArithmetic.StateCheck.first.compose RationalArithmetic.StateCheck.first).pair
    ((RationalArithmetic.StateCheck.first.compose secondCheck).pair secondCheck)
def reset : RationalArithmetic.StateCheck (raw flip s b arity) :=
  ((rowCheck flip).rightMap.compose wireCheck).compose (OrdinaryCoefficient.reset s b arity)
def originalReset : RationalArithmetic.StateCheck (originalRaw s b arity) :=
  ((@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq Unit))).pair RawParentRow.reset).compose (reset false s b arity)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficient
