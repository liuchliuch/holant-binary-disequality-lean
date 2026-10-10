import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCallRun
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicateRaw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall.Raw
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : RawMachine)
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

def states : StateEmbedding m.State (Option Bool × m.State) where
  put state := (none,state)
  get := Prod.snd
  get_put _ := rfl

def program : Label m → Statement m
  | .inl l => Call.statement (states m) Sum.inl (some (.inr (17 : Fin 19))) (m.program l)
  | .inr phase => outside m phase

def machine : RawMachine where
  K := Stack m
  input := oppositeKey m
  output := .inl m.output
  Label := Label m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall.Raw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem erase_call (m : Machine) : RawMachine.erase (machine m) = Raw.machine (RawMachine.erase m) := by
  unfold RawMachine.erase machine Raw.machine
  congr 1
  funext label
  cases label with
  | inl l => rfl
  | inr l => rfl

def rawCheck {r : RawMachine} (h : RationalArithmetic.StateCheck r) : RationalArithmetic.StateCheck (Raw.machine r) where
  inspect state := state.1.isNone && h.inspect state.2
  correct state := by
    rcases state with ⟨flag,state⟩
    cases flag <;> simp [Raw.machine,Bool.and_eq_true,h.correct]

abbrev raw : RawMachine := Raw.machine NeighborPredicate.raw

theorem erase_neighbor : RawMachine.erase (machine NeighborPredicate.machine) = raw := by
  rw [erase_call,NeighborPredicate.erase_machine]

theorem step_eq : HEq raw.view.step (machine NeighborPredicate.machine).computer.step :=
  RawMachine.step_of_erase_eq _ _ erase_neighbor

def reset : RationalArithmetic.StateCheck raw := rawCheck NeighborPredicate.reset

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall
