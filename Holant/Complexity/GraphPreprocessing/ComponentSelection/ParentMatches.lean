import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildPredicate

/-! An actual stored-parent-edge comparison. The optional tag is retained until
the comparison finishes, so a root never matches original edge zero. -/
namespace Holant.Complexity.GraphPreprocessing.ComponentSelection.ParentMatches
open Turing Computability BinaryCompose FixedFieldMachines OriginalCoefficient
open Holant.OneHot.Computable Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false
abbrev Input := ℕ × Graph.ParentRow
def inputEncoding := pairEncoding UnaryBinary.unaryEncoding ParentRowEncoding.row
noncomputable def parentComputes : Computes ParentRowEncoding.row (optionEncoding ParentRowEncoding.endpoint)
    Graph.ParentRow.parent :=
  recode ParentEndpoint.computes id (fun _ => rfl) (fun r => by change ParentRowEncoding.parent.encode r.parent=_; cases r.parent <;> rfl)
noncomputable def edgeComputes : Computes ParentRowEncoding.row (optionEncoding UnaryBinary.unaryEncoding)
    (fun r => r.parent.map Prod.fst) :=
  parentComputes.andThen (OptionMap.computes (Wiring.firstComputes UnaryBinary.unaryEncoding ParentRowEncoding.orientation))
def prepared (x : Input) := (x.2.parent.map Prod.fst).map (fun e => (x.1,e))
noncomputable def prepareComputes : Computes inputEncoding
    (optionEncoding (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)) prepared :=
  (rightMapComputes UnaryBinary.unaryEncoding edgeComputes).andThen
    (OptionContext.computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
def value (x : Input) : Bool := decide (x.2.parent.map Prod.fst=some x.1)
noncomputable def computes : Computes inputEncoding encodingBoolBool value :=
  congrComputes ((prepareComputes.andThen (OptionMap.computes ChildPredicate.comparisonComputes)).andThen OptionAny.computes)
    (fun x => by cases hp : x.2.parent.map Prod.fst <;>
      simp [prepared,ChildPredicate.comparison,OptionAny.value,value,hp,eq_comm])
abbrev edgeMachine : Machine := ParentEndpoint.machine.compose (OptionMap.machine Wiring.firstMachine)
abbrev prepareMachine : Machine := (rightMapMachine edgeMachine).compose OptionContext.machine
abbrev machine : Machine := (prepareMachine.compose (OptionMap.machine WordCompare.machine)).compose OptionAny.machine
@[simp] theorem computes_machine : computes.machine=machine := rfl
theorem inFP : InFP inputEncoding encodingBoolBool value := computes.inFP
end Holant.Complexity.GraphPreprocessing.ComponentSelection.ParentMatches
