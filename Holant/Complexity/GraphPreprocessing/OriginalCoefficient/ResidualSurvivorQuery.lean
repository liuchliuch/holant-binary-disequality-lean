import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQueryInterface
import Holant.Complexity.GraphPreprocessing.ParentRowEncoding

/-! A physical original-endpoint lookup for the surviving residual singleton.
The endpoint orientation is read from the query, not specialized in the control.
The source pin's value bit is physically removed before clean termination. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorQuery
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Stack := ResidualPinQuery.Stack
abbrev Label := ResidualPinQuery.Label
abbrev Statement := ResidualPinQuery.Statement
abbrev inputKey := ResidualPinQuery.inputKey
abbrev temporaryKey := ResidualPinQuery.temporaryKey
abbrev rawKey := ResidualPinQuery.rawKey
abbrev queryKey := ResidualPinQuery.queryKey
abbrev targetKey := ResidualPinQuery.targetKey
abbrev outputKey := ResidualPinQuery.outputKey
abbrev work := ResidualPinQuery.work
abbrev config := ResidualPinQuery.config

def strip : Statement :=
  pop outputKey (fun st bit => (bit,st.2))
    (branch (fun st => st.1 == some true)
      (pop outputKey (fun st bit => (bit,st.2))
        (branch (fun st => st.1 == some true)
          (push outputKey (fun _ => true) (load (fun _ => WordEqual.clean true ()) .halt))
          (goto (fun _ => .inr 12))))
      (branch (fun st => st.1 == some false)
        (push outputKey (fun _ => false) (load (fun _ => WordEqual.clean true ()) .halt))
        (goto (fun _ => .inr 12))))

def controller (i : Fin 13) : Statement := match i.val with
  | 0 => Frame.scanStmt inputKey temporaryKey (.inr 0) (.inr 1) (.inr 12)
  | 1 => copyMoveStmt temporaryKey rawKey (.inr 1) (.inr 2)
  | 2 => Frame.scanStmt inputKey temporaryKey (.inr 2) (.inr 3) (.inr 12)
  | 3 => copyMoveStmt temporaryKey targetKey (.inr 3) (.inr 4)
  | 4 => copyMoveStmt inputKey temporaryKey (.inr 4) (.inr 5)
  | 5 => copyMoveStmt temporaryKey queryKey (.inr 5) (.inl (.inl (.inr 0)))
  | 8 => clearStmt rawKey (.inr 8) (.inr 9)
  | 9 => clearStmt queryKey (.inr 9) (.inr 10)
  | 10 => clearStmt targetKey (.inr 10) (.inr 11)
  | 11 => strip
  | _ => .halt

def program : Label → Statement :=
  Returning.program (ResidualPin.program true) ResidualPinQuery.returns controller

abbrev machine : BinaryCompose.Machine where
  K := Stack
  input := inputKey
  output := outputKey
  Label := Label
  main := .inr 0
  State := WordEqual.Memory Unit
  initial := WordEqual.clean true ()
  program := program

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) :=
  Σ r : {r : RawClosedNetwork // r.WellFormed s b arity},
    Fin r.val.vertices.length × (Fin r.val.edges.length × Bool)

def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool :=
  sigmaEncoding (RawClosedNetwork.validatedEncoding s b arity) (fun r =>
    FixedFieldMachines.pairEncoding (OccurrenceLabel.unaryPortEncoding r.val.vertices.length)
      (FixedFieldMachines.pairEncoding (SignatureLabel.binaryFinEncoding r.val.edges.length)
        ParentRowEncoding.orientation))

@[simp] theorem input_word {s b : ℕ} {arity : ℕ → ℕ} (x : Input s b arity) :
    (inputEncoding s b arity).encode x = Holant.Algebraic.frame (RawClosedNetwork.encoding.encode x.1.val) ++
      (Holant.Algebraic.frame (List.replicate x.2.1.val true) ++
        RawClosedNetwork.endpointEncoding.encode (x.2.2.1.val,x.2.2.2)) := rfl

def portWord (vertex target port : ℕ) : List Bool :=
  if vertex=target then true :: List.replicate port true else [false]

def portBits {s b : ℕ} {arity : ℕ → ℕ} (x : Input s b arity) : List Bool :=
  let p := x.1.val.lookup x.1.property x.2.2
  portWord p.1.val x.2.1.val p.2.val

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorQuery
