import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorInterface

/-! Uniform physical surviving-port selection from an optional original parent
query. Roots take a checked none branch; present parents invoke the actual raw
original-incidence lookup. The target and raw input are always consumed. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOptionalSurvivor
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Stack := ResidualSurvivorQuery.Stack
abbrev Label := ResidualSurvivorQuery.Label
abbrev Statement := ResidualSurvivorQuery.Statement
abbrev inputKey := ResidualSurvivorQuery.inputKey
abbrev temporaryKey := ResidualSurvivorQuery.temporaryKey
abbrev rawKey := ResidualSurvivorQuery.rawKey
abbrev queryKey := ResidualSurvivorQuery.queryKey
abbrev targetKey := ResidualSurvivorQuery.targetKey
abbrev outputKey := ResidualSurvivorQuery.outputKey
abbrev work := ResidualSurvivorQuery.work
abbrev config := ResidualSurvivorQuery.config

def controller (i : Fin 13) : Statement := match i.val with
  | 0 => Frame.scanStmt inputKey temporaryKey (.inr 0) (.inr 1) (.inr 12)
  | 1 => copyMoveStmt temporaryKey rawKey (.inr 1) (.inr 2)
  | 2 => Frame.scanStmt inputKey temporaryKey (.inr 2) (.inr 3) (.inr 12)
  | 3 => copyMoveStmt temporaryKey targetKey (.inr 3) (.inr 4)
  | 4 => pop inputKey (fun st bit => (bit,st.2))
    (branch (fun st => st.1 == some true)
      (load (fun _ => WordEqual.clean true ()) (goto (fun _ => .inr 5)))
      (branch (fun st => st.1 == some false)
        (load (fun _ => WordEqual.clean true ()) (goto (fun _ => .inr 7)))
        (load (fun _ => WordEqual.clean true ()) (goto (fun _ => .inr 12)))))
  | 5 => copyMoveStmt inputKey temporaryKey (.inr 5) (.inr 6)
  | 6 => copyMoveStmt temporaryKey queryKey (.inr 6) (.inl (.inl (.inr 0)))
  | 7 => pop inputKey (fun st bit => (bit,st.2))
    (branch (fun st => st.1.isSome)
      (load (fun _ => WordEqual.clean true ()) (goto (fun _ => .inr 12)))
      (push outputKey (fun _ => false) (load (fun _ => WordEqual.clean true ()) (goto (fun _ => .inr 8)))))
  | 8 => clearStmt rawKey (.inr 8) (.inr 9)
  | 9 => clearStmt queryKey (.inr 9) (.inr 10)
  | 10 => clearStmt targetKey (.inr 10) (.inr 11)
  | 11 => ResidualSurvivorQuery.strip
  | _ => .halt

def program : Label → Statement := Returning.program (ResidualPin.program true) ResidualPinQuery.returns controller

abbrev machine : Machine where
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
    Fin r.val.vertices.length × Option (Fin r.val.edges.length × Bool)

def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool :=
  sigmaEncoding (RawClosedNetwork.validatedEncoding s b arity) (fun r =>
    FixedFieldMachines.pairEncoding (OccurrenceLabel.unaryPortEncoding r.val.vertices.length)
      (optionEncoding (FixedFieldMachines.pairEncoding (SignatureLabel.binaryFinEncoding r.val.edges.length)
        ParentRowEncoding.orientation)))

def portBits {s b : ℕ} {arity : ℕ → ℕ} (x : Input s b arity) : List Bool := match x.2.2 with
  | none => [false]
  | some q => ResidualSurvivorQuery.portBits ⟨x.1,x.2.1,q⟩

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOptionalSurvivor
