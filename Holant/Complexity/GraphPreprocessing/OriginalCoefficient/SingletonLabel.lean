import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SignatureBounds
import Holant.Complexity.GraphPreprocessing.OccurrenceLabel
import Holant.Complexity.GraphPreprocessing.Traversal.CallExits
import Holant.Complexity.FixedFieldMachines.FrameEmit
import Holant.OneHot.StackProgram.Machine.StackWord

/-! Original raw vertex → fixed singleton-assignment coefficient label. The original
network and unary vertex query are retained. Both raw labels and the literal
frame(label) used by TreeEncoding are supported by real bit-stack syntax. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonLabel
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
variable (s b : ℕ) (arity : ℕ → ℕ)
set_option backward.isDefEq.respectTransparency false

abbrev Stack := VertexSignature.Stack ⊕ Fin 2
abbrev RecodeLabel := Bool ⊕ OccurrenceLabel.Input s arity
abbrev Label := VertexSignature.Label ⊕ (RecodeLabel s arity ⊕ Fin 11)
abbrev Statement := Stmt Stack (Label s arity) Unit

def sourceLabel (l : VertexSignature.Label) : Label s arity := .inl l
def literalLabel (l : RecodeLabel s arity) : Label s arity := .inr (.inl l)
def phase (i : Fin 11) : Label s arity := .inr (.inr i)

def signatureKey : Stack := .inl (.inr 4)
def literalKey : Stack := .inl (.inl 1)
def temporaryKey : Stack := .inl (.inl 3)
def outputKey : Stack := .inr 0
def portKey : Stack := .inr 1

def extractorLayout (output port : List Bool) : StackEmbedding VertexSignature.Stack Stack :=
  Returning.layout ![output, port]

def literalLayout (frame : Stack → List Bool) : StackEmbedding Unit Stack where
  key _ := literalKey
  lift source := Function.update frame literalKey (source ())
  lookup source k := by cases k; simp
  update source k word := by
    cases k
    simp only [Function.update_idem, Function.update_self]

def extractReturn (l : VertexSignature.Label) : Option (Label s arity) :=
  some (if l = .inr 12 then phase s arity 9 else phase s arity 8)

def literalReturn : RecodeLabel s arity → Option (Label s arity)
  | .inl true => some (phase s arity 8)
  | _ => some (phase s arity 4)

abbrev recoder := FiniteRecode.machine (OccurrenceLabel.inputEncoding s arity)
  (treeLabelEncoding s b arity) OccurrenceLabel.literal (OccurrenceLabel.inputBound s arity)

def controller (framed : Bool) (i : Fin 11) : Statement s arity :=
  match i.val with
  | 0 => push literalKey (fun _ => true) (goto (fun _ => phase s arity 1))
  | 1 => copyMoveStmt signatureKey temporaryKey (phase s arity 1) (phase s arity 2)
  | 2 => FixedFieldMachines.FrameEmit.delimiterStmt literalKey (phase s arity 3)
  | 3 => FixedFieldMachines.FrameEmit.emitStmt temporaryKey literalKey (phase s arity 3)
      (literalLabel s arity (.inl false))
  | 4 => copyMoveStmt literalKey temporaryKey (phase s arity 4) (phase s arity 5)
  | 5 => if framed then FixedFieldMachines.FrameEmit.delimiterStmt outputKey (phase s arity 6)
      else copyMoveStmt temporaryKey outputKey (phase s arity 5) (phase s arity 7)
  | 6 => FixedFieldMachines.FrameEmit.emitStmt temporaryKey outputKey (phase s arity 6) (phase s arity 7)
  | 9 => copyMoveStmt portKey temporaryKey (phase s arity 9) (phase s arity 10)
  | 10 => copyRestoreStmt portKey literalKey temporaryKey (phase s arity 10) (phase s arity 0)
  | _ => .halt

def program (framed : Bool) : Label s arity → Statement s arity
  | .inl label => embedStmt (extractorLayout [] []) Returning.state (sourceLabel s arity)
      (extractReturn s arity label) (VertexSignature.program label)
  | .inr (.inl label) => embedStmt (literalLayout (fun _ => [])) Returning.state (literalLabel s arity)
      (literalReturn s arity label) ((recoder s b arity).program label)
  | .inr (.inr i) => controller s arity framed i

abbrev machine (framed : Bool) : BinaryCompose.Machine where
  K := Stack
  input := .inl (.inr 0)
  output := outputKey
  Label := Label s arity
  main := sourceLabel s arity (.inr 0)
  State := Option Bool × Unit
  initial := (none, ())
  program := program s b arity framed

def tapes (source : VertexSignature.Stack → List Bool) (output port : List Bool) : Stack → List Bool :=
  Sum.elim source ![output, port]

def outputWord (framed : Bool) (word : List Bool) : List Bool := if framed then Holant.Algebraic.frame word else word

theorem reject_halts (framed : Bool) (work : Stack → List Bool) :
    (machine s b arity framed).computer.step (cfg (phase s arity 8) () work) =
      some (⟨none, (none, ()), work⟩ : Cfg Stack (Label s arity) Unit) := rfl

theorem success_halts (framed : Bool) (work : Stack → List Bool) :
    (machine s b arity framed).computer.step (cfg (phase s arity 7) () work) =
      some (⟨none, (none, ()), work⟩ : Cfg Stack (Label s arity) Unit) := rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonLabel
