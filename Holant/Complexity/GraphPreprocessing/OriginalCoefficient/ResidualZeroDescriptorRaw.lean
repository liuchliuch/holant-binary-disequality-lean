import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroDescriptor
import Holant.Complexity.RationalArithmetic.StateChecks

/-! Exact metadata erasure and structural whole-state observation for the actual
paired residual descriptor machine. These observers are test instrumentation. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroDescriptor
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 512

def raw (a z : Bool) : RawMachine :=
  (RawMachine.erase (ResidualPinQuery.machine false a)).pair
    ((RawMachine.erase (ResidualPinQuery.machine true z)).pair (RawMachine.erase (Constant.machine [false])))

theorem erase_machine (a z : Bool) : RawMachine.erase (machine a z) = raw a z := by
  simp only [machine,raw,RawMachine.erase_pair]

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
  RawMachine.observer_of_erase_eq (machine a z) (raw a z) (erase_machine a z)

def pinCheck (side value : Bool) : RationalArithmetic.StateCheck (RawMachine.erase (ResidualPinQuery.machine side value)) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (WordEqual.Memory Unit)))

def constantCheck : RationalArithmetic.StateCheck (RawMachine.erase (Constant.machine [false])) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))

def reset (a z : Bool) : RationalArithmetic.StateCheck (raw a z) :=
  (pinCheck false a).pair ((pinCheck true z).pair constantCheck)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroDescriptor
