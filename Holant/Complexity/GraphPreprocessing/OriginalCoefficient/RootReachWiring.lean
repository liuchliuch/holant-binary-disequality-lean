import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootReach
import Holant.Complexity.FixedFieldMachines.MachineSyntax

/-! Fixed real wire rearrangement ((vertex count, edge table), root) ->
((vertex count, root), edge table). Every projection, copy, frame and discard is
performed by the existing finite Boolean-stack wiring machines. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootReachWiring
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

def pairWords := pairEncoding Frame.wordEncoding Frame.wordEncoding
def inputEncoding := pairEncoding pairWords Frame.wordEncoding
def value (x : (List Bool × List Bool) × List Bool) : (List Bool × List Bool) × List Bool :=
  ((x.1.1,x.2),x.1.2)

noncomputable def countComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.1.1) :=
  (Wiring.firstComputes pairWords Frame.wordEncoding).andThen (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding)
noncomputable def rootComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.2) :=
  Wiring.secondComputes pairWords Frame.wordEncoding
noncomputable def edgesComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.1.2) :=
  (Wiring.firstComputes pairWords Frame.wordEncoding).andThen (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding)

abbrev countMachine : Machine := Wiring.firstMachine.compose Wiring.firstMachine
abbrev edgesMachine : Machine := Wiring.firstMachine.compose secondMachine
abbrev machine : Machine := pairMachine (pairMachine countMachine secondMachine) edgesMachine

noncomputable def computes : Computes inputEncoding inputEncoding value :=
  pairComputes (pairComputes countComputes rootComputes) edgesComputes

@[simp] theorem computes_machine : computes.machine=machine := rfl
theorem inFP : InFP inputEncoding inputEncoding value := computes.inFP

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootReachWiring
