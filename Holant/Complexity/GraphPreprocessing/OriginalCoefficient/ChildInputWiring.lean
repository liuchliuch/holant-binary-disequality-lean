import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateInterface

/-! Fixed physical rearrangement ((original edges, canonical rows), target)
into (original edges, (target, canonical rows)), the child scanner's entry. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildInputWiring
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

def pairWords := pairEncoding Frame.wordEncoding Frame.wordEncoding
def inputEncoding := pairEncoding pairWords Frame.wordEncoding
def outputEncoding := pairEncoding Frame.wordEncoding pairWords
def value (x : (List Bool × List Bool) × List Bool) := (x.1.1,(x.2,x.1.2))
noncomputable def edgesComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.1.1) :=
  (Wiring.firstComputes pairWords Frame.wordEncoding).andThen (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding)
noncomputable def rowsComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.1.2) :=
  (Wiring.firstComputes pairWords Frame.wordEncoding).andThen (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding)
noncomputable def targetComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.2) :=
  Wiring.secondComputes pairWords Frame.wordEncoding
noncomputable def computes : Computes inputEncoding outputEncoding value :=
  pairComputes edgesComputes (pairComputes targetComputes rowsComputes)
abbrev edgesMachine : Machine := Wiring.firstMachine.compose Wiring.firstMachine
abbrev rowsMachine : Machine := Wiring.firstMachine.compose secondMachine
abbrev machine : Machine := pairMachine edgesMachine (pairMachine secondMachine rowsMachine)
@[simp] theorem computes_machine : computes.machine=machine := rfl
theorem inFP : InFP inputEncoding outputEncoding value := computes.inFP
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildInputWiring
