import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedNonroot
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordCompare
import Holant.Complexity.FixedFieldMachines.MachineSyntax

/-! Physical extraction and unary comparison of the original root and target
fields. Count and edge words are parsed and discarded by actual wire machines. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedFlag
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

def pairWords := pairEncoding Frame.wordEncoding Frame.wordEncoding
def wordEntry := pairEncoding pairWords pairWords
noncomputable def rootWordComputes : Computes wordEntry Frame.wordEncoding (fun x => x.1.2) :=
  (Wiring.firstComputes pairWords pairWords).andThen (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding)
noncomputable def targetWordComputes : Computes wordEntry Frame.wordEncoding (fun x => x.2.1) :=
  (Wiring.secondComputes pairWords pairWords).andThen (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding)
noncomputable def compareComputes : Computes wordEntry encodingBoolBool (fun x => decide (x.1.2=x.2.1)) :=
  (pairComputes rootWordComputes targetWordComputes).andThen WordCompare.computes

abbrev rootMachine : Machine := Wiring.firstMachine.compose secondMachine
abbrev targetMachine : Machine := secondMachine.compose Wiring.firstMachine
abbrev machine : Machine := (pairMachine rootMachine targetMachine).compose WordCompare.machine

def value (x : RootedNonroot.Base) : Bool := decide (x.1.2=x.2.1)
noncomputable def computes : Computes RootedNonroot.baseEncoding encodingBoolBool value :=
  congrComputes (recode compareComputes
    (fun x => ((List.replicate x.1.1 true,List.replicate x.1.2.val true),
      (List.replicate x.2.1.val true,NeighborScan.edgeBits x.2.2))) (fun _ => rfl) (fun _ => rfl))
    (fun x => by simp [value,Fin.ext_iff,List.replicate_inj])
@[simp] theorem computes_machine : computes.machine=machine := rfl
theorem inFP : InFP RootedNonroot.baseEncoding encodingBoolBool value := computes.inFP
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedFlag
