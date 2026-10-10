import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeader
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordJoin

/-! Original parent/child IDs to an actual traversal action chunk. The child's
canonical row is generated from raw bytes, its stored end is flipped, the
original parent's local coefficient is obtained, and the original child ID is
physically emitted as a reference. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := Σ x : RawRootReach.Input s b arity, Fin x.1.val.vertices.length
def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) :=
  sigmaEncoding (RawRootReach.inputEncoding s b arity) (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.vertices.length)
def query (x : Input s b arity) : RawRootReach.Input s b arity := ⟨x.1.1,x.2⟩
def prepared (x : Input s b arity) : ParentCoefficient.Input s b arity :=
  ⟨(x.1,RawParentRow.value (query x)),(ParentCoefficient.originalInput (query x)).property⟩

def words := pairEncoding Frame.wordEncoding Frame.wordEncoding
def wireEncoding := pairEncoding words Frame.wordEncoding
noncomputable def queryWire : Computes wireEncoding words (fun x => (x.1.1,x.2)) :=
  pairComputes ((Wiring.firstComputes words Frame.wordEncoding).andThen (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding))
    (Wiring.secondComputes words Frame.wordEncoding)
noncomputable def queryComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (RawRootReach.inputEncoding s b arity) query :=
  recode queryWire (fun x => ((RawClosedNetwork.encoding.encode x.1.1.val,List.replicate x.1.2.val true),List.replicate x.2.val true))
    (fun _ => rfl) (fun _ => rfl)
noncomputable def parentComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (RawRootReach.inputEncoding s b arity) Sigma.fst :=
  recode (Wiring.firstComputes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding)
    (fun x => (x.1,List.replicate x.2.val true)) (fun _ => rfl) (fun _ => rfl)
noncomputable def prepareComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (ParentCoefficient.inputEncoding s b arity) prepared :=
  recode (pairComputes (parentComputes s b arity)
    ((queryComputes s b arity).andThen (RawParentRow.computes s b arity))) id (fun _ => rfl) (fun _ => rfl)

def portAction (s b : ℕ) (arity : ℕ → ℕ) (a : RawClosedNetwork.TreeLabel s b arity) : List Bool :=
  Traversal.literals (true::Holant.Algebraic.frame ((treeLabelEncoding s b arity).encode a))
noncomputable def portActionComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (treeLabelEncoding s b arity) Frame.wordEncoding (portAction s b arity) :=
  FiniteRecode.computes _ _ _ (lengthBound s b arity) (treeLabelEncoding_length_le s b arity)
abbrev portActionMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  FiniteRecode.machine (treeLabelEncoding s b arity) Frame.wordEncoding (portAction s b arity) (lengthBound s b arity)

noncomputable def referenceComputes : Computes UnaryBinary.unaryEncoding Frame.wordEncoding Traversal.reference :=
  recode (((pairComputes (identityComputes Frame.wordEncoding)
    (constantComputes Frame.wordEncoding Frame.wordEncoding [false])).andThen WordJoin.computes).andThen
    (OrdinaryCoefficient.prefixComputes [true])) (fun n => List.replicate n true) (fun _ => rfl) (fun _ => rfl)
abbrev referenceMachine : Machine :=
  ((pairMachine identityMachine (Constant.machine [false])).compose WordJoin.machine).compose (OrdinaryCoefficient.prefixMachine [true])
noncomputable def childReference (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding (fun x => Traversal.reference x.2.val) :=
  recode ((Wiring.secondComputes (RawRootReach.inputEncoding s b arity) UnaryBinary.unaryEncoding).andThen referenceComputes)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def value (x : Input s b arity) : List Bool :=
  portAction s b arity (ParentCoefficient.value true (prepared x))++Traversal.reference x.2.val
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding value :=
  (pairComputes (((prepareComputes s b arity).andThen (ParentCoefficient.computes true s b arity)).andThen
    (portActionComputes s b arity)) (childReference s b arity)).andThen WordJoin.computes

abbrev queryMachine : Machine := pairMachine (Wiring.firstMachine.compose Wiring.firstMachine) secondMachine
abbrev prepareMachine : Machine := pairMachine Wiring.firstMachine (queryMachine.compose RawParentRow.machine)
abbrev portMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  (prepareMachine.compose (ParentCoefficient.machine true s b arity)).compose (portActionMachine s b arity)
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine (portMachine s b arity) (secondMachine.compose referenceMachine)).compose WordJoin.machine
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine s b arity := rfl
theorem inFP : InFP (inputEncoding s b arity) Frame.wordEncoding value := (computes s b arity).inFP
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild
