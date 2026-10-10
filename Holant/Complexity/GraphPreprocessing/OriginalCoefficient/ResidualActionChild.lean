import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalCoefficient
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildLinear

/-! Conditioned original parent-port labels and original child references.
The child row is physically generated from raw bytes; only its stored original
end is flipped before the two-pin coefficient lookup at the parent vertex. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionChild
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}
abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := Σ x : ResidualContext.Query s b arity, Fin (ResidualContext.source x.1).val.vertices.length
def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) :=
  sigmaEncoding (ResidualContext.queryEncoding s b arity) (fun x => OccurrenceLabel.unaryPortEncoding (ResidualContext.source x.1).val.vertices.length)
def childQuery (x : Input s b arity) : ResidualContext.Query s b arity := ⟨x.1.1,x.2⟩
def parentInput (x : Input s b arity) : ParentCoefficient.Input s b arity :=
  ⟨(ResidualContext.original x.1,RawParentRow.value (ResidualContext.original (childQuery x))),
    (ParentCoefficient.originalInput (ResidualContext.original (childQuery x))).property⟩
def prepared (x : Input s b arity) : ResidualStoredCoefficient.Input s b arity :=
  ⟨⟨parentInput x,ResidualContext.edge x.1.1⟩,x.1.1.property x.2⟩

noncomputable def firstComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (ResidualContext.queryEncoding s b arity) Sigma.fst :=
  recode (Wiring.firstComputes (ResidualContext.queryEncoding s b arity) Frame.wordEncoding)
    (fun x => (x.1,List.replicate x.2.val true)) (fun _ => rfl) (fun _ => rfl)
noncomputable def childComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (ResidualContext.queryEncoding s b arity) childQuery :=
  recode ActionChild.queryWire
    (fun x => (((ResidualContext.encoding s b arity).encode x.1.1,List.replicate x.1.2.val true),List.replicate x.2.val true))
    (fun _ => rfl) (fun _ => rfl)
noncomputable def parentInputComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (ParentCoefficient.inputEncoding s b arity) parentInput :=
  recode (pairComputes ((firstComputes s b arity).andThen (ResidualContext.originalComputes s b arity))
    (((childComputes s b arity).andThen (ResidualContext.originalComputes s b arity)).andThen (RawParentRow.computes s b arity)))
    id (fun _ => rfl) (fun _ => rfl)
noncomputable def prepareComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (ResidualStoredCoefficient.inputEncoding s b arity) prepared :=
  recode (pairComputes (parentInputComputes s b arity) ((firstComputes s b arity).andThen (ResidualContext.edgeComputes s b arity)))
    id (fun _ => rfl) (fun _ => rfl)
def portValue (a z : Bool) (x : Input s b arity) := ResidualStoredCoefficient.value true a z (prepared x)
noncomputable def portComputes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (treeLabelEncoding s b arity) (portValue a z) :=
  (prepareComputes s b arity).andThen (ResidualStoredCoefficient.computes true a z s b arity)
noncomputable def referenceComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding (fun x => Traversal.reference x.2.val) :=
  recode ((Wiring.secondComputes (ResidualContext.queryEncoding s b arity) UnaryBinary.unaryEncoding).andThen ActionChild.referenceComputes)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
def value (a z : Bool) (x : Input s b arity) := ActionChild.portAction s b arity (portValue a z x)++Traversal.reference x.2.val
noncomputable def computes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding (value a z) :=
  (pairComputes ((portComputes a z s b arity).andThen (ActionChildLinear.renderComputes s b arity))
    (referenceComputes s b arity)).andThen WordJoin.computes

abbrev parentInputMachine := pairMachine (Wiring.firstMachine.compose ResidualContext.originalMachine)
  ((ActionChild.queryMachine.compose ResidualContext.originalMachine).compose RawParentRow.machine)
abbrev prepareMachine := pairMachine parentInputMachine (Wiring.firstMachine.compose ResidualContext.edgeMachine)
abbrev portMachine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) := prepareMachine.compose (ResidualStoredCoefficient.machine true a z s b arity)
abbrev machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine ((portMachine a z s b arity).compose ActionChildLinear.renderMachine)
    (secondMachine.compose ActionChild.referenceMachine)).compose WordJoin.machine
@[simp] theorem computes_machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : (computes a z s b arity).machine=machine a z s b arity := rfl
theorem inFP (a z : Bool) : InFP (inputEncoding s b arity) Frame.wordEncoding (value a z) := (computes a z s b arity).inFP
theorem output_length (a z : Bool) (x : Input s b arity) : (value a z x).length≤4*lengthBound s b arity+x.2.val+6 := by
  have h := treeLabelEncoding_length_le s b arity (portValue a z x)
  simp only [value,ActionChild.portAction,List.length_append,Traversal.literals_length,List.length_cons,
    Holant.Algebraic.frame_length,Traversal.reference_length]
  omega
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionChild
