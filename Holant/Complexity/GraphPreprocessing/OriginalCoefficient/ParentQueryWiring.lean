import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedParent

/-! Fixed Boolean-stack rearrangement of a computed component root, actual
vertex-count/edge table, and original target. The root word is physically copied
for the final row and the parent query; all framing/projection costs are charged. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentQueryWiring
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

def pairWords := pairEncoding Frame.wordEncoding Frame.wordEncoding
def tableTarget := pairEncoding pairWords Frame.wordEncoding
def inputEncoding := pairEncoding Frame.wordEncoding tableTarget
def outputEncoding := pairEncoding Frame.wordEncoding (pairEncoding pairWords pairWords)
def value (x : List Bool × ((List Bool × List Bool) × List Bool)) :=
  (x.1,((x.2.1.1,x.1),(x.2.2,x.2.1.2)))

noncomputable def rootComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.1) := Wiring.firstComputes _ _
noncomputable def tailComputes : Computes inputEncoding tableTarget (fun x => x.2) := Wiring.secondComputes _ _
noncomputable def tableComputes : Computes inputEncoding pairWords (fun x => x.2.1) := tailComputes.andThen (Wiring.firstComputes _ _)
noncomputable def countComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.2.1.1) := tableComputes.andThen (Wiring.firstComputes _ _)
noncomputable def edgeComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.2.1.2) := tableComputes.andThen (Wiring.secondComputes _ _)
noncomputable def targetComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.2.2) := tailComputes.andThen (Wiring.secondComputes _ _)
noncomputable def computes : Computes inputEncoding outputEncoding value :=
  pairComputes rootComputes (pairComputes (pairComputes countComputes rootComputes) (pairComputes targetComputes edgeComputes))

abbrev tableMachine : Machine := secondMachine.compose Wiring.firstMachine
abbrev countMachine : Machine := tableMachine.compose Wiring.firstMachine
abbrev edgeMachine : Machine := tableMachine.compose secondMachine
abbrev targetMachine : Machine := secondMachine.compose secondMachine
abbrev machine : Machine := pairMachine Wiring.firstMachine
  (pairMachine (pairMachine countMachine Wiring.firstMachine) (pairMachine targetMachine edgeMachine))
@[simp] theorem computes_machine : computes.machine=machine := rfl
theorem inFP : InFP inputEncoding outputEncoding value := computes.inFP
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentQueryWiring
