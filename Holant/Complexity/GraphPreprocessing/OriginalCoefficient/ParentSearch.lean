import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundInterface

/-! Finite first-hit parent search. An immutable-layer provider returns a
framed next bitmap and the original-edge parent option. The initial bitmap
physically allocates the round budget; each attempt adds a unary depth token.
The successful branch erases every retained stream and emits the literal
framed depth followed by the exact provider parent word. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

abbrev Stack := BitmapRound.Stack m
abbrev Label := m.Label ⊕ (Fin 3 ⊕ Fin 32)
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)
def phase (i : Fin 32) : Label m := .inr (.inr i)
abbrev tableKey : Stack m := BitmapRound.tableKey m
abbrev cursorKey : Stack m := BitmapRound.cursorKey m
abbrev indexKey : Stack m := BitmapRound.indexKey m
abbrev temporaryKey : Stack m := BitmapRound.temporaryKey m
abbrev edgesKey : Stack m := BitmapRound.edgesKey m
abbrev outputKey : Stack m := BitmapRound.outputKey m
abbrev copyKey : Stack m := BitmapRound.copyKey m
abbrev inputKey : Stack m := BitmapRound.inputKey m

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

def program : Label m → Statement m
  | .inl l => Call.statement (LeftMap.states m) Sum.inl (some (phase m 13)) (m.program l)
  | .inr (.inl l) => embedStmt (BitmapRound.snapshotLayout m (fun _ => [])) (BitmapRound.snapshotStates m)
      (fun l => .inr (.inl l)) (some (phase m 4)) (BitmapSnapshot.program l)
  | .inr (.inr l) => outside m l

abbrev machine : Machine where
  K := Stack m
  input := inputKey m
  output := .inl m.output
  Label := Label m
  main := phase m 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

def config (l : Label m) (source : m.K → List Bool) (table cursor index temporary edges output copy input : List Bool) :=
  cfg l m.initial (BitmapRound.tapes m source table cursor index temporary edges output copy input)
def ready (l : Label m) (table cursor index edges output input : List Bool) :=
  config m l (fun _ => []) table cursor index [] edges output [] input

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
