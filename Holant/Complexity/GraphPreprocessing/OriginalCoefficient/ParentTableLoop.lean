import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentRow
import Holant.Complexity.GraphPreprocessing.Call
import Holant.Complexity.FixedFieldMachines.LeftMap

/-! Physical original-vertex table loop. The executed count package supplies
V unary tokens; each original vertex is queried once in descending order and
its exact row is framed and prepended. One physically emitted list terminator
makes even the empty graph's parent table canonical. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Stack := m.K ⊕ Fin 7
abbrev Label := m.Label ⊕ Fin 24
abbrev Memory := Option Bool × m.State
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Memory m)

def rawKey : Stack m := .inr 0
def indexKey : Stack m := .inr 1
def outputKey : Stack m := .inr 2
def temporaryKey : Stack m := .inr 3
def rawCopyKey : Stack m := .inr 4
def verticesKey : Stack m := .inr 5
def inputKey : Stack m := .inr 6

def outside (i : Fin 24) : Statement m := match i.val with
  | 0 => Frame.scanStmt (inputKey m) (temporaryKey m) (.inr 0) (.inr 1) (.inr 23)
  | 1 => copyMoveStmt (temporaryKey m) (rawKey m) (.inr 1) (.inr 2)
  | 2 => Frame.scanStmt (inputKey m) (temporaryKey m) (.inr 2) (.inr 3) (.inr 23)
  | 3 => copyMoveStmt (temporaryKey m) (indexKey m) (.inr 3) (.inr 4)
  | 4 => clearStmt (inputKey m) (.inr 4) (.inr 5)
  | 5 => push (outputKey m) (fun _ => false) (goto (fun _ => .inr 6))
  | 6 => pop (indexKey m) (fun st bit => (bit,st.2))
    (branch (fun st => st.1.isSome)
      (load (fun st => (none,st.2)) (goto (fun _ => .inr 7)))
      (load (fun st => (none,st.2)) (goto (fun _ => .inr 18))))
  | 7 => copyMoveStmt (indexKey m) (temporaryKey m) (.inr 7) (.inr 8)
  | 8 => copyRestoreStmt (indexKey m) (.inl m.input) (temporaryKey m) (.inr 8) (.inr 9)
  | 9 => copyMoveStmt (rawKey m) (temporaryKey m) (.inr 9) (.inr 10)
  | 10 => copyRestoreStmt (rawKey m) (rawCopyKey m) (temporaryKey m) (.inr 10) (.inr 11)
  | 11 => copyMoveStmt (rawCopyKey m) (temporaryKey m) (.inr 11) (.inr 12)
  | 12 => FrameEmit.delimiterStmt (.inl m.input) (.inr 13)
  | 13 => FrameEmit.emitStmt (temporaryKey m) (.inl m.input) (.inr 13) (.inl m.main)
  | 14 => copyMoveStmt (.inl m.output) (temporaryKey m) (.inr 14) (.inr 15)
  | 15 => FrameEmit.delimiterStmt (outputKey m) (.inr 16)
  | 16 => FrameEmit.emitStmt (temporaryKey m) (outputKey m) (.inr 16) (.inr 17)
  | 17 => push (outputKey m) (fun _ => true) (goto (fun _ => .inr 6))
  | 18 => clearStmt (rawKey m) (.inr 18) (.inr 22)
  | 23 => load (fun _ => (some false,m.initial)) .halt
  | _ => .halt

def program : Label m → Statement m
  | .inl l => Call.statement (LeftMap.states m) Sum.inl (some (.inr (14 : Fin 24))) (m.program l)
  | .inr i => outside m i

abbrev machine : Machine where
  K := Stack m
  input := inputKey m
  output := outputKey m
  Label := Label m
  main := .inr 0
  State := Memory m
  initial := (none,m.initial)
  program := program m

def extras (raw index output temporary rawCopy vertices input : List Bool) : Fin 7 → List Bool :=
  ![raw,index,output,temporary,rawCopy,vertices,input]

def tapes (source : m.K → List Bool) (raw index output temporary rawCopy vertices input : List Bool) : Stack m → List Bool :=
  Sum.elim source (extras raw index output temporary rawCopy vertices input)

def config (l : Label m) (source : m.K → List Bool)
    (raw index output temporary rawCopy vertices input : List Bool) :=
  cfg l m.initial (tapes m source raw index output temporary rawCopy vertices input)

/-- No source-machine tape is initialized by a host word-valued instruction. -/
def cleanConfig (l : Label m) (raw index output vertices input : List Bool) :=
  config m l (fun _ => []) raw index output [] [] vertices input

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop
