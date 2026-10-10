import Holant.Complexity.GraphPreprocessing.Call
import Holant.Complexity.FixedFieldMachines.LeftMap

/-! A real returning word-list traversal with one preserved context. Every list
entry executes the provider on frame(context) ++ entry. Output chunks are
physically reversed into an accumulator and restored in original list order. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false
abbrev Stack := m.K ⊕ Fin 6
abbrev Label := m.Label ⊕ Fin 16
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)
def inputKey : Stack m := .inr 0
def contextKey : Stack m := .inr 1
def temporaryKey : Stack m := .inr 2
def copyKey : Stack m := .inr 3
def reverseKey : Stack m := .inr 4
def outputKey : Stack m := .inr 5

def outside (i : Fin 16) : Statement m := match i.val with
  | 0 => Frame.scanStmt (inputKey m) (temporaryKey m) (.inr 0) (.inr 1) (.inr 15)
  | 1 => copyMoveStmt (temporaryKey m) (contextKey m) (.inr 1) (.inr 2)
  | 2 => pop (inputKey m) (fun st bit => (bit,st.2))
    (branch (fun st => st.1==some true)
      (load (fun st => (none,st.2)) (goto (fun _ => .inr 3)))
      (branch (fun st => st.1==some false)
        (load (fun st => (none,st.2)) (goto (fun _ => .inr 9)))
        (load (fun st => (none,st.2)) (goto (fun _ => .inr 15)))))
  | 3 => Frame.scanStmt (inputKey m) (temporaryKey m) (.inr 3) (.inr 4) (.inr 15)
  | 4 => copyMoveStmt (temporaryKey m) (.inl m.input) (.inr 4) (.inr 5)
  | 5 => copyMoveStmt (contextKey m) (temporaryKey m) (.inr 5) (.inr 6)
  | 6 => copyRestoreStmt (contextKey m) (copyKey m) (temporaryKey m) (.inr 6) (.inr 7)
  | 7 => copyMoveStmt (copyKey m) (temporaryKey m) (.inr 7) (.inr 8)
  | 8 => FrameEmit.delimiterStmt (.inl m.input) (.inr 10)
  | 10 => FrameEmit.emitStmt (temporaryKey m) (.inl m.input) (.inr 10) (.inl m.main)
  | 11 => copyMoveStmt (.inl m.output) (reverseKey m) (.inr 11) (.inr 2)
  | 9 => pop (inputKey m) (fun st bit => (bit,st.2))
    (branch (fun st => st.1.isSome)
      (load (fun st => (none,st.2)) (goto (fun _ => .inr 15)))
      (load (fun st => (none,st.2)) (goto (fun _ => .inr 12))))
  | 12 => clearStmt (contextKey m) (.inr 12) (.inr 13)
  | 13 => copyMoveStmt (reverseKey m) (outputKey m) (.inr 13) (.inr 14)
  | 15 => load (fun _ => (some false,m.initial)) .halt
  | _ => .halt
def program : Label m → Statement m
  | .inl label => Call.statement (LeftMap.states m) Sum.inl (some (.inr (11 : Fin 16))) (m.program label)
  | .inr label => outside m label
abbrev machine : Machine where
  K := Stack m
  input := inputKey m
  output := outputKey m
  Label := Label m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m
def extras (input context temporary copied rev output : List Bool) : Fin 6 → List Bool :=
  ![input,context,temporary,copied,rev,output]
def tapes (source : m.K → List Bool) (input context temporary copied rev output : List Bool) : Stack m → List Bool :=
  Sum.elim source (extras input context temporary copied rev output)
def config (label : Label m) (source : m.K → List Bool) (input context temporary copied rev output : List Bool) :=
  cfg label m.initial (tapes m source input context temporary copied rev output)
def ready (label : Label m) (input context rev output : List Bool) :=
  config m label (fun _ => []) input context [] [] rev output
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
