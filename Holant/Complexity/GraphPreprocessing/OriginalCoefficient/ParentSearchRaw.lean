import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearchSpec
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentProbeExecution

/-! Finite first-hit parent search. An immutable-layer provider returns a
framed next bitmap and the original-edge parent option. The initial bitmap
physically allocates the round budget; each attempt adds a unary depth token.
The successful branch erases every retained stream and emits the literal
framed depth followed by the exact provider parent word. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch.Raw
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : RawMachine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

abbrev Stack := BitmapRound.Raw.Stack m
abbrev Label := m.Label ⊕ (Fin 3 ⊕ Fin 32)
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)
def phase (i : Fin 32) : Label m := .inr (.inr i)
abbrev tableKey : Stack m := BitmapRound.Raw.tableKey m
abbrev cursorKey : Stack m := BitmapRound.Raw.cursorKey m
abbrev indexKey : Stack m := BitmapRound.Raw.indexKey m
abbrev temporaryKey : Stack m := BitmapRound.Raw.temporaryKey m
abbrev edgesKey : Stack m := BitmapRound.Raw.edgesKey m
abbrev outputKey : Stack m := BitmapRound.Raw.outputKey m
abbrev copyKey : Stack m := BitmapRound.Raw.copyKey m
abbrev inputKey : Stack m := BitmapRound.Raw.inputKey m

def outside (i : Fin 32) : Statement m := match i.val with
  | 0 => Frame.scanStmt (inputKey m) (temporaryKey m) (phase m 0) (phase m 1) (phase m 31)
  | 1 => copyMoveStmt (temporaryKey m) (tableKey m) (phase m 1) (phase m 2)
  | 2 => copyMoveStmt (inputKey m) (temporaryKey m) (phase m 2) (phase m 3)
  | 3 => copyMoveStmt (temporaryKey m) (edgesKey m) (phase m 3) (.inr (.inl 0))
  | 4 => clearStmt (cursorKey m) (phase m 4) (phase m 5)
  | 5 => pop (indexKey m) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (push (outputKey m) (fun _ => true) (load (fun v => (none,v.2)) (goto (fun _ => phase m 6))))
      (load (fun v => (none,v.2)) (goto (fun _ => phase m 31))))
  | 6 => copyMoveStmt (edgesKey m) (temporaryKey m) (phase m 6) (phase m 7)
  | 7 => copyRestoreStmt (edgesKey m) (.inl m.input) (temporaryKey m) (phase m 7) (phase m 8)
  | 8 => copyMoveStmt (tableKey m) (temporaryKey m) (phase m 8) (phase m 9)
  | 9 => copyRestoreStmt (tableKey m) (copyKey m) (temporaryKey m) (phase m 9) (phase m 10)
  | 10 => copyMoveStmt (copyKey m) (temporaryKey m) (phase m 10) (phase m 11)
  | 11 => FrameEmit.delimiterStmt (.inl m.input) (phase m 12)
  | 12 => FrameEmit.emitStmt (temporaryKey m) (.inl m.input) (phase m 12) (.inl m.main)
  | 13 => Frame.scanStmt (.inl m.output) (temporaryKey m) (phase m 13) (phase m 14) (phase m 31)
  | 14 => copyMoveStmt (temporaryKey m) (cursorKey m) (phase m 14) (phase m 15)
  | 15 => pop (.inl m.output) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun v => (none,v.2)) (goto (fun _ => phase m 22)))
        (load (fun v => (none,v.2)) (goto (fun _ => phase m 16))))
      (load (fun v => (none,v.2)) (goto (fun _ => phase m 31))))
  | 16 => clearStmt (tableKey m) (phase m 16) (phase m 17)
  | 17 => copyMoveStmt (cursorKey m) (temporaryKey m) (phase m 17) (phase m 18)
  | 18 => copyMoveStmt (temporaryKey m) (tableKey m) (phase m 18) (phase m 5)
  | 22 => push (.inl m.output) (fun _ => true) (goto (fun _ => phase m 23))
  | 23 => clearStmt (tableKey m) (phase m 23) (phase m 24)
  | 24 => clearStmt (cursorKey m) (phase m 24) (phase m 25)
  | 25 => clearStmt (indexKey m) (phase m 25) (phase m 26)
  | 26 => clearStmt (edgesKey m) (phase m 26) (phase m 27)
  | 27 => copyMoveStmt (outputKey m) (temporaryKey m) (phase m 27) (phase m 28)
  | 28 => FrameEmit.delimiterStmt (.inl m.output) (phase m 29)
  | 29 => FrameEmit.emitStmt (temporaryKey m) (.inl m.output) (phase m 29) (phase m 30)
  | 31 => load (fun _ => (some false,m.initial)) .halt
  | _ => .halt

def states : StateEmbedding m.State (Option Bool × m.State) where
  put state := (none,state)
  get := Prod.snd
  get_put _ := rfl

def program : Label m → Statement m
  | .inl l => Call.statement (states m) Sum.inl (some (phase m 13)) (m.program l)
  | .inr (.inl l) => embedStmt (BitmapRound.Raw.snapshotLayout m (fun _ => [])) (BitmapRound.Raw.snapshotStates m)
      (fun l => .inr (.inl l)) (some (phase m 4)) (BitmapSnapshot.program l)
  | .inr (.inr l) => outside m l

def machine : RawMachine where
  K := Stack m
  input := inputKey m
  output := .inl m.output
  Label := Label m
  main := phase m 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch.Raw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem erase_iterator (m : Machine) : RawMachine.erase (machine m) = Raw.machine (RawMachine.erase m) := by
  unfold RawMachine.erase machine Raw.machine
  congr 1
  funext label
  cases label with
  | inl l => rfl
  | inr l => cases l with
    | inl l => rfl
    | inr l => rfl

abbrev raw : RawMachine := Raw.machine ParentProbe.raw

theorem erase_actual : RawMachine.erase (machine actual) = raw := by
  rw [erase_iterator,ParentProbe.erase_machine]

theorem step_eq : HEq raw.view.step (machine actual).computer.step := RawMachine.step_of_erase_eq _ _ erase_actual

theorem start_eq : HEq raw.view.start (initList (machine actual).computer) := RawMachine.start_of_erase_eq _ _ erase_actual

theorem observer_eq :
    letI : Fintype (machine actual).K := (machine actual).finiteK
    letI : DecidableEq (machine actual).K := (machine actual).decidableK
    HEq raw.view.observeHalt (fun c : (machine actual).Config =>
      (c.stk (machine actual).output,decide (∀ k, k ≠ (machine actual).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_actual

def reset : RationalArithmetic.StateCheck raw where
  inspect state := state.1.isNone && ParentProbe.reset.inspect state.2
  correct state := by
    rcases state with ⟨flag,state⟩
    cases flag <;> simp [raw,Raw.machine,ParentProbe.reset.correct]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
