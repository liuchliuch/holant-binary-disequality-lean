import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualVertexInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawRootReach

/-! Direct raw-network/original-vertex/descriptor entry to the real original
coefficient-label emitter. No deleted edge or dummy edge is part of this input;
ordinary no-pin descriptors and actual residual descriptors share the loader. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexDescriptor
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable (s b : ℕ) (arity : ℕ → ℕ)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 512

abbrev Stack := ResidualVertex.Stack ⊕ Fin 3
abbrev Label := ResidualVertex.Label s arity ⊕ Fin 14
instance : Fintype (Label s arity) := by
  letI : Fintype (ResidualVertex.Label s arity) := (ResidualVertex.machine s 0 arity false).finiteLabel
  exact inferInstanceAs (Fintype (ResidualVertex.Label s arity ⊕ Fin 14))
abbrev Statement := Stmt Stack (Label s arity) Unit

def inputKey : Stack := .inr 0
def contextKey : Stack := .inr 1
def temporaryKey : Stack := .inr 2
def rawKey : Stack := .inl (.inl (.inr 0))
def vertexKey : Stack := .inl (.inl (.inr 1))
def descriptorKey : Stack := .inl ResidualVertex.descriptorKey
def outputKey : Stack := .inl ResidualVertex.outputKey

def returns : ResidualVertex.Label s arity → Fin 14
  | .inr (.inr i) => if i=7 then 9 else 13
  | _ => 13

def controller (i : Fin 14) : Statement s arity := match i.val with
  | 0 => Frame.scanStmt inputKey temporaryKey (.inr 0) (.inr 1) (.inr 13)
  | 1 => copyMoveStmt temporaryKey contextKey (.inr 1) (.inr 2)
  | 2 => Frame.scanStmt contextKey temporaryKey (.inr 2) (.inr 3) (.inr 13)
  | 3 => copyMoveStmt temporaryKey rawKey (.inr 3) (.inr 4)
  | 4 => copyMoveStmt contextKey temporaryKey (.inr 4) (.inr 5)
  | 5 => copyMoveStmt temporaryKey vertexKey (.inr 5) (.inr 7)
  | 7 => copyMoveStmt inputKey temporaryKey (.inr 7) (.inr 8)
  | 8 => copyMoveStmt temporaryKey descriptorKey (.inr 8) (.inl (ResidualVertex.sourceLabel s arity (.inr 0)))
  | 9 => clearStmt rawKey (.inr 9) (.inr 10)
  | 10 => clearStmt vertexKey (.inr 10) (.inr 11)
  | 11 => clearStmt descriptorKey (.inr 11) (.inr 12)
  | 13 => load (fun _ => (some false,())) .halt
  | _ => .halt

def program : Label s arity → Statement s arity :=
  Returning.program (ResidualVertex.program s b arity false) (returns s arity) (controller s arity)

abbrev machine : BinaryCompose.Machine where
  K := Stack
  input := inputKey
  output := outputKey
  Label := Label s arity
  main := .inr 0
  State := Option Bool × Unit
  initial := (none,())
  program := program s b arity

def work (input context raw vertex descriptor output temporary : List Bool) : Stack → List Bool :=
  Sum.elim (ResidualVertex.work raw vertex descriptor [] [] [] output) ![input,context,temporary]

def config (label : Label s arity) (input context raw vertex descriptor output temporary : List Bool) :=
  cfg label () (work input context raw vertex descriptor output temporary)

abbrev Input := Σ x : RawRootReach.Input s b arity,
  ResidualLabel.Descriptor (arity (x.1.val.vertices.get x.2).1)

def inputEncoding : Encoding (Input s b arity) Bool :=
  sigmaEncoding (RawRootReach.inputEncoding s b arity)
    (fun x => ResidualLabel.descriptorEncoding (arity (x.1.val.vertices.get x.2).1))

def literal (x : Input s b arity) : RawClosedNetwork.TreeLabel s b arity :=
  ResidualVertex.label x.1.1.val x.1.1.property x.1.2 x.2

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexDescriptor
