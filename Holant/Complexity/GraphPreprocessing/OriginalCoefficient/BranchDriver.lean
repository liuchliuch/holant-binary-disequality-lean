import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentOptionInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionChoiceInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMapRaw

/-! A finite selective compiler driver. Both selectors physically read the
retained classification/query word, but only a present input invokes its real
provider. This is ordinary optional-machine composition with counted copies,
parsing, returned words and unselected-result cleanup. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BranchDriver
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {A B C : Type} {ea : Encoding A Bool} {eb : Encoding B Bool} {ec : Encoding C Bool}
  {tree : A → Option B} {cycle : A → Option C} {treeCode : B → List Bool} {cycleCode : C → List Bool}
def value (fallback : List Bool) (tree : A → Option B) (cycle : A → Option C)
    (treeCode : B → List Bool) (cycleCode : C → List Bool) (x : A) :=
  (tree x).map treeCode |>.getD ((cycle x).map cycleCode |>.getD fallback)
noncomputable def computes (fallback : List Bool)
    (st : Computes ea (optionEncoding eb) tree) (sc : Computes ea (optionEncoding ec) cycle)
    (wt : Computes eb Frame.wordEncoding treeCode) (wc : Computes ec Frame.wordEncoding cycleCode) :
    Computes ea Frame.wordEncoding (value fallback tree cycle treeCode cycleCode) :=
  (pairComputes (st.andThen (OptionMap.computes wt)) (sc.andThen (OptionMap.computes wc))).andThen
    (OptionChoice.computes fallback)
def machine (fallback : List Bool) (st sc wt wc : Machine) : Machine :=
  (pairMachine (st.compose (OptionMap.machine wt)) (sc.compose (OptionMap.machine wc))).compose (OptionChoice.machine fallback)
@[simp] theorem computes_machine (fallback : List Bool)
    (st : Computes ea (optionEncoding eb) tree) (sc : Computes ea (optionEncoding ec) cycle)
    (wt : Computes eb Frame.wordEncoding treeCode) (wc : Computes ec Frame.wordEncoding cycleCode) :
    (computes fallback st sc wt wc).machine=machine fallback st.machine sc.machine wt.machine wc.machine := rfl

def raw (fallback : List Bool) (st sc wt wc : RawMachine) : RawMachine :=
  ((st.compose (OptionMap.Raw.machine wt)).pair (sc.compose (OptionMap.Raw.machine wc))).compose
    (RawMachine.erase (OptionChoice.machine fallback))
theorem erase_machine (fallback : List Bool) (st sc wt wc : Machine) :
    RawMachine.erase (machine fallback st sc wt wc)=raw fallback (RawMachine.erase st) (RawMachine.erase sc)
      (RawMachine.erase wt) (RawMachine.erase wc) := by
  rw [machine,RawMachine.erase_compose,RawMachine.erase_pair,RawMachine.erase_compose,OptionMap.erase_machine,
    RawMachine.erase_compose,OptionMap.erase_machine]
  rfl

def reset (fallback : List Bool) {st sc wt wc : RawMachine}
    (hst : RationalArithmetic.StateCheck st) (hsc : RationalArithmetic.StateCheck sc)
    (hwt : RationalArithmetic.StateCheck wt) (hwc : RationalArithmetic.StateCheck wc) :
    RationalArithmetic.StateCheck (raw fallback st sc wt wc) :=
  ((hst.compose (OptionMap.rawCheck hwt)).pair (hsc.compose (OptionMap.rawCheck hwc))).compose
    (@RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit))))
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BranchDriver
