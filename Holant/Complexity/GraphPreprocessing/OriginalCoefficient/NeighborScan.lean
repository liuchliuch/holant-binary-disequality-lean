import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCallRun
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.UnaryField

/-! Actual original-order endpoint scan. Each edge is tested at its false end
then its true end using the retained old bitmap. The physical unary edge counter
is advanced only after both tests fail. A successful result carries the original
edge ID and orientation; EOF gives none. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

abbrev Stack := NeighborCall.Stack m ⊕ Fin 5
abbrev Label := NeighborCall.Label m ⊕ Fin 48
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)

def inputKey : Stack m := .inr 0
def indexKey : Stack m := .inr 1
def holdKey : Stack m := .inr 2
def sideKey : Stack m := .inr 3
def outputKey : Stack m := .inr 4
def tableKey : Stack m := .inl (NeighborCall.tableKey m)
def targetKey : Stack m := .inl (NeighborCall.targetKey m)
def endpointKey : Stack m := .inl (NeighborCall.endpointKey m)
def oppositeKey : Stack m := .inl (NeighborCall.oppositeKey m)
def temporaryKey : Stack m := .inl (NeighborCall.temporaryKey m)
def resultKey : Stack m := .inl (.inl m.output)

def returns : NeighborCall.Label m → Fin 48
  | .inl _ => 47
  | .inr phase => if phase=17 then 7 else 47

def outside (phase : Fin 48) : Statement m := match phase.val with
  | 0 => Frame.scanStmt (inputKey m) (temporaryKey m) (.inr 0) (.inr 1) (.inr 47)
  | 1 => copyMoveStmt (temporaryKey m) (tableKey m) (.inr 1) (.inr 2)
  | 2 => Frame.scanStmt (inputKey m) (temporaryKey m) (.inr 2) (.inr 3) (.inr 47)
  | 3 => copyMoveStmt (temporaryKey m) (targetKey m) (.inr 3) (.inr 4)
  | 4 => peek (inputKey m) (fun v bit => (bit,v.2))
    (load (fun v => v)
      (branch (fun v => v.1.isSome)
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 5)))
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 40)))))
  | 5 => UnaryField.statement (inputKey m) (endpointKey m) (.inr 5) (.inr 6) (.inr 47)
  | 6 => UnaryField.statement (inputKey m) (oppositeKey m) (.inr 6) (.inl (.inr 0)) (.inr 47)
  | 7 => pop (resultKey m) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 16)))
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 8))))
      (load (fun v => (none,v.2)) (goto (fun _ => .inr 47))))
  | 8 => pop (sideKey m) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (load (fun v => (none,v.2)) (goto (fun _ => .inr 22)))
      (load (fun v => (none,v.2)) (goto (fun _ => .inr 9))))
  | 9 => copyMoveStmt (endpointKey m) (temporaryKey m) (.inr 9) (.inr 10)
  | 10 => copyMoveStmt (temporaryKey m) (holdKey m) (.inr 10) (.inr 11)
  | 11 => copyMoveStmt (oppositeKey m) (temporaryKey m) (.inr 11) (.inr 12)
  | 12 => copyMoveStmt (temporaryKey m) (endpointKey m) (.inr 12) (.inr 13)
  | 13 => copyMoveStmt (holdKey m) (temporaryKey m) (.inr 13) (.inr 14)
  | 14 => copyMoveStmt (temporaryKey m) (oppositeKey m) (.inr 14) (.inr 15)
  | 15 => push (sideKey m) (fun _ => true) (goto (fun _ => .inl (.inr 0)))
  | 16 => pop (sideKey m) (fun v bit => (bit,v.2))
    (push (outputKey m) (fun v => v.1.getD false)
      (load (fun v => (none,v.2)) (goto (fun _ => .inr 17))))
  | 17 => copyMoveStmt (indexKey m) (temporaryKey m) (.inr 17) (.inr 18)
  | 18 => FrameEmit.delimiterStmt (outputKey m) (.inr 19)
  | 19 => FrameEmit.emitStmt (temporaryKey m) (outputKey m) (.inr 19) (.inr 20)
  | 20 => push (outputKey m) (fun _ => true) (goto (fun _ => .inr 30))
  | 22 => clearStmt (endpointKey m) (.inr 22) (.inr 23)
  | 23 => clearStmt (oppositeKey m) (.inr 23) (.inr 24)
  | 24 => push (indexKey m) (fun _ => true) (goto (fun _ => .inr 4))
  | 30 => clearStmt (inputKey m) (.inr 30) (.inr 31)
  | 31 => clearStmt (tableKey m) (.inr 31) (.inr 32)
  | 32 => clearStmt (targetKey m) (.inr 32) (.inr 33)
  | 33 => clearStmt (endpointKey m) (.inr 33) (.inr 34)
  | 34 => clearStmt (oppositeKey m) (.inr 34) (.inr 35)
  | 35 => clearStmt (indexKey m) (.inr 35) (.inr 36)
  | 40 => push (outputKey m) (fun _ => false) (goto (fun _ => .inr 30))
  | 47 => load (fun _ => (some false,m.initial)) .halt
  | _ => .halt

def program : Label m → Statement m := Returning.program (NeighborCall.machine m).program (returns m) (outside m)

abbrev machine : Machine where
  K := Stack m
  input := inputKey m
  output := outputKey m
  Label := Label m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

def inputWord (table target : List Bool) (edges : List (ℕ × ℕ)) : List Bool :=
  Holant.Algebraic.frame table ++ (Holant.Algebraic.frame target ++ ReachRound.encode edges)

def extras (input index hold side output : List Bool) : Fin 5 → List Bool := ![input,index,hold,side,output]
def tapes (source : m.K → List Bool) (table target endpoint opposite temporary copy comparison input index hold side output : List Bool) :
    Stack m → List Bool :=
  Sum.elim (NeighborCall.tapes m source table target endpoint opposite temporary copy comparison)
    (extras input index hold side output)
def config (label : Label m) (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output : List Bool) :=
  cfg label m.initial (tapes m source table target endpoint opposite temporary copy comparison input index hold side output)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
