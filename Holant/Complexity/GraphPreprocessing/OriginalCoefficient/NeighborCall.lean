import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicate
import Holant.Complexity.GraphPreprocessing.Call
import Holant.Complexity.FixedFieldMachines.LeftMap

/-! A finite physical call kernel for an oriented neighbor predicate. It copies
the preserved bitmap and three unary vertex words, builds the exact nested
pair/framing format, calls an actual finite provider, and returns with its full
caller frame retained. No input word is installed by a semantic callback. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Stack := m.K ⊕ Fin 7
abbrev Label := m.Label ⊕ Fin 19
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)

def tableKey : Stack m := .inr 0
def targetKey : Stack m := .inr 1
def endpointKey : Stack m := .inr 2
def oppositeKey : Stack m := .inr 3
def temporaryKey : Stack m := .inr 4
def copyKey : Stack m := .inr 5
def comparisonKey : Stack m := .inr 6

def outside (phase : Fin 19) : Statement m := match phase.val with
  | 0 => copyMoveStmt (oppositeKey m) (temporaryKey m) (.inr 0) (.inr 1)
  | 1 => copyRestoreStmt (oppositeKey m) (.inl m.input) (temporaryKey m) (.inr 1) (.inr 2)
  | 2 => copyMoveStmt (tableKey m) (temporaryKey m) (.inr 2) (.inr 3)
  | 3 => copyRestoreStmt (tableKey m) (copyKey m) (temporaryKey m) (.inr 3) (.inr 4)
  | 4 => copyMoveStmt (copyKey m) (temporaryKey m) (.inr 4) (.inr 5)
  | 5 => FrameEmit.delimiterStmt (.inl m.input) (.inr 6)
  | 6 => FrameEmit.emitStmt (temporaryKey m) (.inl m.input) (.inr 6) (.inr 7)
  | 7 => copyMoveStmt (endpointKey m) (temporaryKey m) (.inr 7) (.inr 8)
  | 8 => copyRestoreStmt (endpointKey m) (comparisonKey m) (temporaryKey m) (.inr 8) (.inr 9)
  | 9 => copyMoveStmt (targetKey m) (temporaryKey m) (.inr 9) (.inr 10)
  | 10 => copyRestoreStmt (targetKey m) (copyKey m) (temporaryKey m) (.inr 10) (.inr 11)
  | 11 => copyMoveStmt (copyKey m) (temporaryKey m) (.inr 11) (.inr 12)
  | 12 => FrameEmit.delimiterStmt (comparisonKey m) (.inr 13)
  | 13 => FrameEmit.emitStmt (temporaryKey m) (comparisonKey m) (.inr 13) (.inr 14)
  | 14 => copyMoveStmt (comparisonKey m) (temporaryKey m) (.inr 14) (.inr 15)
  | 15 => FrameEmit.delimiterStmt (.inl m.input) (.inr 16)
  | 16 => FrameEmit.emitStmt (temporaryKey m) (.inl m.input) (.inr 16) (.inl m.main)
  | _ => .halt

def program : Label m → Statement m
  | .inl l => Call.statement (LeftMap.states m) Sum.inl (some (.inr (17 : Fin 19))) (m.program l)
  | .inr phase => outside m phase

abbrev machine : Machine where
  K := Stack m
  input := oppositeKey m
  output := .inl m.output
  Label := Label m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

def extras (table target endpoint opposite temporary copy comparison : List Bool) : Fin 7 → List Bool :=
  ![table,target,endpoint,opposite,temporary,copy,comparison]

def tapes (source : m.K → List Bool) (table target endpoint opposite temporary copy comparison : List Bool) :
    Stack m → List Bool := Sum.elim source (extras table target endpoint opposite temporary copy comparison)

def config (label : Label m) (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison : List Bool) :=
  cfg label m.initial (tapes m source table target endpoint opposite temporary copy comparison)

def queryWord (table target endpoint opposite : List Bool) : List Bool :=
  Holant.Algebraic.frame (Holant.Algebraic.frame target ++ endpoint) ++
    (Holant.Algebraic.frame table ++ opposite)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall
