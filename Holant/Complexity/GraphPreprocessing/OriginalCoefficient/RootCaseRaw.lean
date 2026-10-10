import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCaseCall
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedNonrootRaw
import Holant.Complexity.FixedFieldMachines.LeftMap
import Holant.Complexity.GraphPreprocessing.Call

/-! A physical framed Boolean selects the root case or a real parent machine.
The root case erases its input and emits depth zero / no parent. The nonroot
case copies the actual input into the provider and returns its clean word. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCase.Raw
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : RawMachine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

abbrev Stack := m.K ⊕ Fin 3
abbrev Label := m.Label ⊕ Fin 16
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)
def phase (i : Fin 16) : Label m := .inr i
def inputKey : Stack m := .inr 0
def temporaryKey : Stack m := .inr 1
def outputKey : Stack m := .inr 2

def outside (i : Fin 16) : Statement m := match i.val with
  | 0 => Frame.scanStmt (inputKey m) (temporaryKey m) (phase m 0) (phase m 1) (phase m 15)
  | 1 => copyMoveStmt (temporaryKey m) (outputKey m) (phase m 1) (phase m 2)
  | 2 => pop (outputKey m) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun v => (none,v.2)) (goto (fun _ => phase m 8)))
        (load (fun v => (none,v.2)) (goto (fun _ => phase m 3))))
      (load (fun v => (none,v.2)) (goto (fun _ => phase m 15))))
  | 3 => copyMoveStmt (inputKey m) (temporaryKey m) (phase m 3) (phase m 4)
  | 4 => copyMoveStmt (temporaryKey m) (.inl m.input) (phase m 4) (.inl m.main)
  | 5 => copyMoveStmt (.inl m.output) (temporaryKey m) (phase m 5) (phase m 6)
  | 6 => copyMoveStmt (temporaryKey m) (outputKey m) (phase m 6) (phase m 7)
  | 8 => clearStmt (inputKey m) (phase m 8) (phase m 9)
  | 9 => push (outputKey m) (fun _ => false) (push (outputKey m) (fun _ => false) (goto (fun _ => phase m 7)))
  | 15 => load (fun _ => (some false,m.initial)) .halt
  | _ => .halt

def states : StateEmbedding m.State (Option Bool × m.State) where
  put state := (none,state)
  get := Prod.snd
  get_put _ := rfl

def program : Label m → Statement m
  | .inl l => Call.statement (states m) Sum.inl (some (phase m 5)) (m.program l)
  | .inr l => outside m l
def machine : RawMachine where
  K := Stack m
  input := inputKey m
  output := outputKey m
  Label := Label m
  main := phase m 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCase.Raw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCase
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

theorem erase_branch (m : Machine) : RawMachine.erase (machine m) = Raw.machine (RawMachine.erase m) := by
  unfold RawMachine.erase machine Raw.machine
  congr 1
  funext label
  cases label <;> rfl

def reset {m : RawMachine} (h : RationalArithmetic.StateCheck m) : RationalArithmetic.StateCheck (Raw.machine m) where
  inspect state := state.1.isNone && h.inspect state.2
  correct state := by
    rcases state with ⟨flag,state⟩
    cases flag <;> simp [Raw.machine,h.correct]
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCase
