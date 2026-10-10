import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficient

/-! Fixed physical rearrangement of (raw, vertex, optional parent) and cut ID
into the existing residual-parent provider's literal four-field protocol. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredWiring
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false
def pairWords := pairEncoding Frame.wordEncoding Frame.wordEncoding
def sourceWords := pairEncoding Frame.wordEncoding pairWords
def inputEncoding := pairEncoding sourceWords Frame.wordEncoding
def outputEncoding := pairEncoding Frame.wordEncoding (pairEncoding Frame.wordEncoding pairWords)
def value (x : (List Bool × (List Bool × List Bool)) × List Bool) := (x.1.1,(x.1.2.1,(x.2,x.1.2.2)))
noncomputable def rawComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.1.1) :=
  (Wiring.firstComputes sourceWords Frame.wordEncoding).andThen (Wiring.firstComputes Frame.wordEncoding pairWords)
noncomputable def tailComputes : Computes inputEncoding pairWords (fun x => x.1.2) :=
  (Wiring.firstComputes sourceWords Frame.wordEncoding).andThen (Wiring.secondComputes Frame.wordEncoding pairWords)
noncomputable def vertexComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.1.2.1) :=
  tailComputes.andThen (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding)
noncomputable def parentComputes : Computes inputEncoding Frame.wordEncoding (fun x => x.1.2.2) :=
  tailComputes.andThen (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding)
noncomputable def computes : Computes inputEncoding outputEncoding value :=
  pairComputes rawComputes (pairComputes vertexComputes
    (pairComputes (Wiring.secondComputes sourceWords Frame.wordEncoding) parentComputes))
abbrev rawMachine : Machine := Wiring.firstMachine.compose Wiring.firstMachine
abbrev tailMachine : Machine := Wiring.firstMachine.compose secondMachine
abbrev vertexMachine : Machine := tailMachine.compose Wiring.firstMachine
abbrev parentMachine : Machine := tailMachine.compose secondMachine
abbrev machine : Machine := pairMachine rawMachine (pairMachine vertexMachine (pairMachine secondMachine parentMachine))
@[simp] theorem computes_machine : computes.machine=machine := rfl
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredWiring
