import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundInterface

/-! Physical bounded iteration of an actual bitmap-round provider. The number
of iterations is allocated by scanning the initial bitmap, not supplied as a
time certificate. Every call loads a fresh framed bitmap and retained edge word;
the old bitmap is erased and replaced by the actual returned word. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

abbrev Stack := BitmapRound.Stack m
abbrev Label := m.Label ⊕ (Fin 3 ⊕ Fin 24)
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)
def phase (i : Fin 24) : Label m := .inr (.inr i)
abbrev tableKey : Stack m := BitmapRound.tableKey m
abbrev cursorKey : Stack m := BitmapRound.cursorKey m
abbrev indexKey : Stack m := BitmapRound.indexKey m
abbrev temporaryKey : Stack m := BitmapRound.temporaryKey m
abbrev edgesKey : Stack m := BitmapRound.edgesKey m
abbrev outputKey : Stack m := BitmapRound.outputKey m
abbrev copyKey : Stack m := BitmapRound.copyKey m
abbrev inputKey : Stack m := BitmapRound.inputKey m

def outside (i : Fin 24) : Statement m := match i.val with
  | 0 => Frame.scanStmt (inputKey m) (temporaryKey m) (phase m 0) (phase m 1) (phase m 23)
  | 1 => copyMoveStmt (temporaryKey m) (tableKey m) (phase m 1) (phase m 2)
  | 2 => copyMoveStmt (inputKey m) (temporaryKey m) (phase m 2) (phase m 3)
  | 3 => copyMoveStmt (temporaryKey m) (edgesKey m) (phase m 3) (.inr (.inl 0))
  | 4 => clearStmt (cursorKey m) (phase m 4) (phase m 5)
  | 5 => pop (indexKey m) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (load (fun v => (none,v.2)) (goto (fun _ => phase m 6)))
      (load (fun v => (none,v.2)) (goto (fun _ => phase m 18))))
  | 6 => copyMoveStmt (edgesKey m) (temporaryKey m) (phase m 6) (phase m 7)
  | 7 => copyRestoreStmt (edgesKey m) (.inl m.input) (temporaryKey m) (phase m 7) (phase m 8)
  | 8 => copyMoveStmt (tableKey m) (temporaryKey m) (phase m 8) (phase m 9)
  | 9 => copyRestoreStmt (tableKey m) (copyKey m) (temporaryKey m) (phase m 9) (phase m 10)
  | 10 => copyMoveStmt (copyKey m) (temporaryKey m) (phase m 10) (phase m 11)
  | 11 => FrameEmit.delimiterStmt (.inl m.input) (phase m 12)
  | 12 => FrameEmit.emitStmt (temporaryKey m) (.inl m.input) (phase m 12) (.inl m.main)
  | 13 => clearStmt (tableKey m) (phase m 13) (phase m 14)
  | 14 => copyMoveStmt (.inl m.output) (temporaryKey m) (phase m 14) (phase m 15)
  | 15 => copyMoveStmt (temporaryKey m) (tableKey m) (phase m 15) (phase m 5)
  | 18 => clearStmt (edgesKey m) (phase m 18) (phase m 19)
  | 19 => copyMoveStmt (tableKey m) (temporaryKey m) (phase m 19) (phase m 20)
  | 20 => copyMoveStmt (temporaryKey m) (outputKey m) (phase m 20) (phase m 21)
  | 23 => load (fun _ => (some false,m.initial)) .halt
  | _ => .halt

def program : Label m → Statement m
  | .inl l => Call.statement (LeftMap.states m) Sum.inl (some (phase m 13)) (m.program l)
  | .inr (.inl l) => embedStmt (BitmapRound.snapshotLayout m (fun _ => [])) (BitmapRound.snapshotStates m)
      (fun l => .inr (.inl l)) (some (phase m 4)) (BitmapSnapshot.program l)
  | .inr (.inr l) => outside m l

abbrev machine : Machine where
  K := Stack m
  input := inputKey m
  output := outputKey m
  Label := Label m
  main := phase m 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

def config (l : Label m) (source : m.K → List Bool) (table cursor index temporary edges output copy input : List Bool) :=
  cfg l m.initial (BitmapRound.tapes m source table cursor index temporary edges output copy input)
def ready (l : Label m) (table cursor index edges output input : List Bool) :=
  config m l (fun _ => []) table cursor index [] edges output [] input

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterate
