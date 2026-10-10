import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.PortBounds
import Holant.Complexity.GraphPreprocessing.ParentRowEncoding
import Holant.Complexity.GraphPreprocessing.SignatureLabel
import Holant.OneHot.StackProgram.Machine.StackWord

/-! Clean original endpoint-to-vertex query through the actual raw inverse
incidence search. The original local port is found and then physically erased;
only its original vertex coordinate remains as a unary output. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointVertex
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 512
set_option Elab.async false

abbrev Stack := PortLookup.Stack ⊕ Fin 2
abbrev Label := PortLookup.Label ⊕ Fin 9
abbrev Statement := WordEqual.Statement Stack Label Unit

def inputKey : Stack := .inr 0
def temporaryKey : Stack := .inr 1
def rawKey : Stack := .inl PortLookup.rawKey
def queryKey : Stack := .inl PortLookup.queryKey
def portKey : Stack := .inl PortLookup.portKey
def outputKey : Stack := .inl PortLookup.vertexKey

def returns (l : PortLookup.Label) : Fin 9 := if l = .inr 8 then 4 else 8

def controller (i : Fin 9) : Statement := match i.val with
  | 0 => Frame.scanStmt inputKey temporaryKey (.inr 0) (.inr 1) (.inr 8)
  | 1 => copyMoveStmt temporaryKey rawKey (.inr 1) (.inr 2)
  | 2 => copyMoveStmt inputKey temporaryKey (.inr 2) (.inr 3)
  | 3 => copyMoveStmt temporaryKey queryKey (.inr 3) (.inl (.inr 0))
  | 4 => clearStmt rawKey (.inr 4) (.inr 5)
  | 5 => clearStmt queryKey (.inr 5) (.inr 6)
  | 6 => clearStmt portKey (.inr 6) (.inr 7)
  | 8 => load (fun _ => WordEqual.clean false ()) .halt
  | _ => .halt

def program : Label → Statement := Returning.program PortLookup.program returns controller

abbrev machine : Machine where
  K := Stack
  input := inputKey
  output := outputKey
  Label := Label
  main := .inr 0
  State := WordEqual.Memory Unit
  initial := WordEqual.clean true ()
  program := program

def work (input raw query vertex port temporary : List Bool) : Stack → List Bool :=
  Sum.elim (PortLookup.tapes [] [] port [] [] vertex raw query []) ![input,temporary]

def config (l : Label) (input raw query vertex port temporary : List Bool) :=
  WordEqual.cfg l true () (work input raw query vertex port temporary)

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) :=
  Σ r : {r : RawClosedNetwork // r.WellFormed s b arity}, Fin r.val.edges.length × Bool

def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool :=
  sigmaEncoding (RawClosedNetwork.validatedEncoding s b arity) (fun r =>
    FixedFieldMachines.pairEncoding (SignatureLabel.binaryFinEncoding r.val.edges.length) ParentRowEncoding.orientation)

@[simp] theorem input_word {s b : ℕ} {arity : ℕ → ℕ} (x : Input s b arity) :
    (inputEncoding s b arity).encode x = Holant.Algebraic.frame (RawClosedNetwork.encoding.encode x.1.val) ++
      RawClosedNetwork.endpointEncoding.encode (x.2.1.val,x.2.2) := rfl

def vertexBits {s b : ℕ} {arity : ℕ → ℕ} (x : Input s b arity) : List Bool :=
  List.replicate (x.1.val.lookup x.1.property x.2).1.val true

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointVertex
