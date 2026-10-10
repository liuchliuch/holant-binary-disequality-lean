import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapSnapshot
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanInterface
import Holant.Complexity.GraphPreprocessing.Call

/-! Finite synchronous bitmap-round controller. The original bitmap is restored
before any predicate call. Its reversed physical cursor supplies each old bit,
and a counter allocated from those actual bits supplies descending original IDs.
New bits are prepended, producing the original vertex order. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

abbrev Stack := m.K ⊕ Fin 9
abbrev Label := m.Label ⊕ (Fin 3 ⊕ Fin 32)
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)
def phase (i : Fin 32) : Label m := .inr (.inr i)
def tableKey : Stack m := .inr 0
def cursorKey : Stack m := .inr 1
def indexKey : Stack m := .inr 2
def temporaryKey : Stack m := .inr 3
def edgesKey : Stack m := .inr 4
def outputKey : Stack m := .inr 5
def copyKey : Stack m := .inr 6
def inputKey : Stack m := .inr 7

/-- A fixed injection of four snapshot stacks, with every caller tape retained. -/
def snapshotLayout (frame : Stack m → List Bool) : StackEmbedding (Fin 4) (Stack m) where
  key i := .inr (i.castLE (by decide))
  lift source := Sum.elim (fun k => frame (.inl k))
    (fun j => if h : j.val<4 then source ⟨j.val,h⟩ else frame (.inr j))
  lookup source i := by simp [Fin.castLE,i.isLt]
  update source i word := by
    funext k
    cases k with
    | inl k => simp [Function.update]
    | inr j =>
      by_cases hj : j.val<4
      · have he : j=i.castLE (by decide) ↔ (⟨j.val,hj⟩ : Fin 4)=i := by simp [Fin.ext_iff]
        simp [Function.update,hj,he]
      · have hn : j≠i.castLE (by decide) := by
          intro h; subst j; exact hj i.isLt
        simp [Function.update,hj,hn]

def snapshotStates : StateEmbedding (Option Bool × Unit) (Option Bool × m.State) where
  put state := (state.1,m.initial)
  get state := (state.1,())
  get_put state := by rcases state with ⟨bit,u⟩; cases u; rfl

def outside (i : Fin 32) : Statement m := match i.val with
  | 0 => Frame.scanStmt (inputKey m) (temporaryKey m) (phase m 0) (phase m 1) (phase m 31)
  | 1 => copyMoveStmt (temporaryKey m) (tableKey m) (phase m 1) (phase m 2)
  | 2 => copyMoveStmt (inputKey m) (temporaryKey m) (phase m 2) (phase m 3)
  | 3 => copyMoveStmt (temporaryKey m) (edgesKey m) (phase m 3) (.inr (.inl 0))
  | 4 => pop (indexKey m) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (pop (cursorKey m) (fun v bit => (bit,v.2))
        (branch (fun v => v.1.isSome)
          (branch (fun v => v.1.getD false)
            (load (fun v => (none,v.2)) (goto (fun _ => phase m 5)))
            (load (fun v => (none,v.2)) (goto (fun _ => phase m 6))))
          (load (fun v => (none,v.2)) (goto (fun _ => phase m 31)))))
      (load (fun v => (none,v.2)) (goto (fun _ => phase m 25))))
  | 5 => push (outputKey m) (fun _ => true) (goto (fun _ => phase m 4))
  | 6 => copyMoveStmt (edgesKey m) (temporaryKey m) (phase m 6) (phase m 7)
  | 7 => copyRestoreStmt (edgesKey m) (.inl m.input) (temporaryKey m) (phase m 7) (phase m 8)
  | 8 => copyMoveStmt (indexKey m) (temporaryKey m) (phase m 8) (phase m 9)
  | 9 => copyRestoreStmt (indexKey m) (copyKey m) (temporaryKey m) (phase m 9) (phase m 10)
  | 10 => copyMoveStmt (copyKey m) (temporaryKey m) (phase m 10) (phase m 11)
  | 11 => FrameEmit.delimiterStmt (.inl m.input) (phase m 12)
  | 12 => FrameEmit.emitStmt (temporaryKey m) (.inl m.input) (phase m 12) (phase m 13)
  | 13 => copyMoveStmt (tableKey m) (temporaryKey m) (phase m 13) (phase m 14)
  | 14 => copyRestoreStmt (tableKey m) (copyKey m) (temporaryKey m) (phase m 14) (phase m 15)
  | 15 => copyMoveStmt (copyKey m) (temporaryKey m) (phase m 15) (phase m 16)
  | 16 => FrameEmit.delimiterStmt (.inl m.input) (phase m 17)
  | 17 => FrameEmit.emitStmt (temporaryKey m) (.inl m.input) (phase m 17) (.inl m.main)
  | 18 => pop (.inl m.output) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (push (outputKey m) (fun v => v.1.getD false)
        (load (fun v => (none,v.2)) (goto (fun _ => phase m 19))))
      (load (fun v => (none,v.2)) (goto (fun _ => phase m 31))))
  | 19 => clearStmt (.inl m.output) (phase m 19) (phase m 4)
  | 25 => clearStmt (tableKey m) (phase m 25) (phase m 26)
  | 26 => clearStmt (edgesKey m) (phase m 26) (phase m 27)
  | 27 => clearStmt (cursorKey m) (phase m 27) (phase m 28)
  | 31 => load (fun _ => (some false,m.initial)) .halt
  | _ => .halt

def program : Label m → Statement m
  | .inl l => Call.statement (LeftMap.states m) Sum.inl (some (phase m 18)) (m.program l)
  | .inr (.inl l) => embedStmt (snapshotLayout m (fun _ => [])) (snapshotStates m)
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

def extras (table cursor index temporary edges output copy input : List Bool) : Fin 9 → List Bool :=
  ![table,cursor,index,temporary,edges,output,copy,input,[]]
def tapes (source : m.K → List Bool) (table cursor index temporary edges output copy input : List Bool) : Stack m → List Bool :=
  Sum.elim source (extras table cursor index temporary edges output copy input)
def config (l : Label m) (source : m.K → List Bool) (table cursor index temporary edges output copy input : List Bool) :=
  cfg l m.initial (tapes m source table cursor index temporary edges output copy input)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
