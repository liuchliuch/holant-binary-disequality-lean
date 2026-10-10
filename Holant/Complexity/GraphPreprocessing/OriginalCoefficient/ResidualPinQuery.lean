import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinInterface
import Holant.Complexity.FixedFieldMachines.FrameEmit
import Holant.Complexity.FixedFieldMachines.LeftMap

/-! Clean original raw/vertex/edge query interface for the real residual-pin
producer. Input parsing, endpoint framing and final input cleanup are explicit
finite Boolean-stack operations. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQuery
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxRecDepth 4096

abbrev Stack := ResidualPin.Stack ⊕ Fin 2
abbrev Label := ResidualPin.Label ⊕ Fin 13
instance : DecidableEq Stack := by unfold Stack; infer_instance
instance : Fintype Stack := by unfold Stack; infer_instance
abbrev Statement := WordEqual.Statement Stack Label Unit

def inputKey : Stack := .inr 0
def temporaryKey : Stack := .inr 1
def rawKey : Stack := .inl ResidualPin.rawKey
def queryKey : Stack := .inl ResidualPin.queryKey
def targetKey : Stack := .inl ResidualPin.targetKey
def outputKey : Stack := .inl ResidualPin.outputKey

def returns (l : ResidualPin.Label) : Fin 13 := if l = .inr 8 then 8 else 12

def controller (side : Bool) (i : Fin 13) : Statement := match i.val with
  | 0 => Frame.scanStmt inputKey temporaryKey (.inr 0) (.inr 1) (.inr 12)
  | 1 => copyMoveStmt temporaryKey rawKey (.inr 1) (.inr 2)
  | 2 => Frame.scanStmt inputKey temporaryKey (.inr 2) (.inr 3) (.inr 12)
  | 3 => copyMoveStmt temporaryKey targetKey (.inr 3) (.inr 4)
  | 4 => push queryKey (fun _ => side) (goto (fun _ => .inr 5))
  | 5 => copyMoveStmt inputKey temporaryKey (.inr 5) (.inr 6)
  | 6 => FixedFieldMachines.FrameEmit.delimiterStmt queryKey (.inr 7)
  | 7 => FixedFieldMachines.FrameEmit.emitStmt temporaryKey queryKey (.inr 7) (.inl (.inl (.inr 0)))
  | 8 => clearStmt rawKey (.inr 8) (.inr 9)
  | 9 => clearStmt queryKey (.inr 9) (.inr 10)
  | 10 => clearStmt targetKey (.inr 10) (.inr 11)
  | _ => .halt

def program (side value : Bool) : Label → Statement := Returning.program (ResidualPin.program value) returns (controller side)

abbrev machine (side value : Bool) : BinaryCompose.Machine where
  K := Stack
  input := inputKey
  output := outputKey
  Label := Label
  main := .inr 0
  State := WordEqual.Memory Unit
  initial := WordEqual.clean true ()
  program := program side value

def work (input raw query target output temporary : List Bool) : Stack → List Bool :=
  Sum.elim (ResidualPin.work raw query [] [] target [] [] output) ![input,temporary]

def config (label : Label) (input raw query target output temporary : List Bool) :=
  WordEqual.cfg label true () (work input raw query target output temporary)

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) :=
  Σ r : {r : RawClosedNetwork // r.WellFormed s b arity}, Fin r.val.vertices.length × Fin r.val.edges.length

def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool :=
  sigmaEncoding (RawClosedNetwork.validatedEncoding s b arity) (fun r =>
    FixedFieldMachines.pairEncoding (OccurrenceLabel.unaryPortEncoding r.val.vertices.length)
      (SignatureLabel.binaryFinEncoding r.val.edges.length))

@[simp] theorem input_word {s b : ℕ} {arity : ℕ → ℕ} (x : Input s b arity) :
    (inputEncoding s b arity).encode x = Holant.Algebraic.frame (RawClosedNetwork.encoding.encode x.1.val) ++
      (Holant.Algebraic.frame (List.replicate x.2.1.val true) ++ encodeNat x.2.2.val) := rfl

def pinBits {s b : ℕ} {arity : ℕ → ℕ} (side value : Bool) (x : Input s b arity) : List Bool :=
  let p := x.1.val.lookup x.1.property (x.2.2,side)
  ResidualPin.pinWord value p.1.val x.2.1.val p.2.val

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQuery
