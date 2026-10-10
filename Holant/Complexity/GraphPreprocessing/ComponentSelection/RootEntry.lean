import Holant.Complexity.GraphPreprocessing.ComponentSelection.SelectedEntry
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentEndpointInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordCompare
import Holant.Complexity.FixedFieldMachines.Constant
import Holant.Complexity.FixedFieldMachines.MachineSyntax

/-! An original parent row emits its component ID precisely in the parent-none
case. Every reader, comparison and framing operation is a finite tape program. -/
namespace Holant.Complexity.GraphPreprocessing.ComponentSelection.RootEntry
open Turing Computability BinaryCompose FixedFieldMachines OriginalCoefficient
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

noncomputable def componentComputes : Computes ParentRowEncoding.row Frame.wordEncoding
    (fun r => List.replicate r.component true) :=
  recode (Wiring.firstComputes UnaryBinary.unaryEncoding
    (pairEncoding UnaryBinary.unaryEncoding ParentRowEncoding.parent))
    (fun r => (r.component,(r.depth,r.parent))) (fun _ => rfl) (fun _ => rfl)
noncomputable def parentWordComputes : Computes ParentRowEncoding.row Frame.wordEncoding
    (fun r => ParentRowEncoding.parent.encode r.parent) :=
  recode ParentEndpoint.computes id (fun _ => rfl) (fun _ => rfl)
noncomputable def rootComputes : Computes ParentRowEncoding.row encodingBoolBool
    (fun r => decide (r.parent=none)) :=
  congrComputes ((pairComputes parentWordComputes
    (constantComputes ParentRowEncoding.row Frame.wordEncoding [false])).andThen WordCompare.computes)
    (fun r => by cases h : r.parent <;> simp [WordCompare.value,h,ParentRowEncoding.parent])
def value (r : Graph.ParentRow) : List Bool :=
  if r.parent=none then true::Holant.Algebraic.frame (List.replicate r.component true) else []
noncomputable def computes : Computes ParentRowEncoding.row Frame.wordEncoding value :=
  congrComputes ((pairComputes rootComputes componentComputes).andThen SelectedEntry.computes)
    (fun r => by simp [SelectedEntry.value,value])
abbrev rootMachine : Machine := (pairMachine ParentEndpoint.machine (Constant.machine [false])).compose WordCompare.machine
abbrev machine : Machine := (pairMachine rootMachine Wiring.firstMachine).compose SelectedEntry.machine
@[simp] theorem computes_machine : computes.machine=machine := rfl
theorem inFP : InFP ParentRowEncoding.row Frame.wordEncoding value := computes.inFP
end Holant.Complexity.GraphPreprocessing.ComponentSelection.RootEntry
