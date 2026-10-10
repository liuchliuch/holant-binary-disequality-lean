import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildPredicate
import Holant.Complexity.GraphPreprocessing.Call

/-! Original-order child filtering. Actual row frames are consumed once, a
physical unary counter tracks their original positions, and every row invokes
the finite child predicate. Matched IDs are emitted in reversed bit order and
one final physical reversal restores increasing original vertex order. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

abbrev Stack := m.K ⊕ Fin 9
abbrev Label := m.Label ⊕ Fin 48
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)
def inputKey : Stack m := .inr 0
def edgesKey : Stack m := .inr 1
def targetKey : Stack m := .inr 2
def indexKey : Stack m := .inr 3
def rowKey : Stack m := .inr 4
def temporaryKey : Stack m := .inr 5
def copyKey : Stack m := .inr 6
def reverseKey : Stack m := .inr 7
def outputKey : Stack m := .inr 8

def outside (l : Fin 48) : Statement m := match l.val with
  | 0 => Frame.scanStmt (inputKey m) (temporaryKey m) (.inr 0) (.inr 1) (.inr 47)
  | 1 => copyMoveStmt (temporaryKey m) (edgesKey m) (.inr 1) (.inr 2)
  | 2 => Frame.scanStmt (inputKey m) (temporaryKey m) (.inr 2) (.inr 3) (.inr 47)
  | 3 => copyMoveStmt (temporaryKey m) (targetKey m) (.inr 3) (.inr 4)
  | 4 => pop (inputKey m) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 5)))
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 30))))
      (load (fun _ => (some false,m.initial)) (goto (fun _ => .inr 47))))
  | 5 => Frame.scanStmt (inputKey m) (temporaryKey m) (.inr 5) (.inr 6) (.inr 47)
  | 6 => copyMoveStmt (temporaryKey m) (rowKey m) (.inr 6) (.inr 7)
  | 7 => copyMoveStmt (rowKey m) (temporaryKey m) (.inr 7) (.inr 8)
  | 8 => copyMoveStmt (temporaryKey m) (.inl m.input) (.inr 8) (.inr 9)
  | 9 => copyMoveStmt (edgesKey m) (temporaryKey m) (.inr 9) (.inr 10)
  | 10 => copyRestoreStmt (edgesKey m) (copyKey m) (temporaryKey m) (.inr 10) (.inr 11)
  | 11 => copyMoveStmt (copyKey m) (temporaryKey m) (.inr 11) (.inr 12)
  | 12 => FrameEmit.delimiterStmt (.inl m.input) (.inr 13)
  | 13 => FrameEmit.emitStmt (temporaryKey m) (.inl m.input) (.inr 13) (.inr 14)
  | 14 => copyMoveStmt (targetKey m) (temporaryKey m) (.inr 14) (.inr 15)
  | 15 => copyRestoreStmt (targetKey m) (copyKey m) (temporaryKey m) (.inr 15) (.inr 16)
  | 16 => copyMoveStmt (copyKey m) (temporaryKey m) (.inr 16) (.inr 17)
  | 17 => FrameEmit.delimiterStmt (.inl m.input) (.inr 18)
  | 18 => FrameEmit.emitStmt (temporaryKey m) (.inl m.input) (.inr 18) (.inl m.main)
  | 19 => pop (.inl m.output) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 20)))
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 25))))
      (load (fun _ => (some false,m.initial)) (goto (fun _ => .inr 47))))
  | 20 => push (reverseKey m) (fun _ => true) (goto (fun _ => .inr 21))
  | 21 => copyMoveStmt (indexKey m) (temporaryKey m) (.inr 21) (.inr 22)
  | 22 => copyRestoreStmt (indexKey m) (copyKey m) (temporaryKey m) (.inr 22) (.inr 23)
  | 23 => pop (copyKey m) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (push (reverseKey m) (fun _ => true) (push (reverseKey m) (fun _ => true)
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 23)))))
      (push (reverseKey m) (fun _ => false) (load (fun v => (none,v.2)) (goto (fun _ => .inr 25)))))
  | 25 => push (indexKey m) (fun _ => true) (goto (fun _ => .inr 4))
  | 30 => clearStmt (edgesKey m) (.inr 30) (.inr 31)
  | 31 => clearStmt (targetKey m) (.inr 31) (.inr 32)
  | 32 => clearStmt (indexKey m) (.inr 32) (.inr 33)
  | 33 => push (reverseKey m) (fun _ => false) (goto (fun _ => .inr 34))
  | 34 => copyMoveStmt (reverseKey m) (outputKey m) (.inr 34) (.inr 35)
  | 35 => pop (inputKey m) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (load (fun _ => (some false,m.initial)) .halt)
      (load (fun _ => (none,m.initial)) .halt))
  | 47 => load (fun _ => (some false,m.initial)) .halt
  | _ => .halt

def program : Label m → Statement m
  | .inl l => Call.statement (LeftMap.states m) Sum.inl (some (.inr (19 : Fin 48))) (m.program l)
  | .inr l => outside m l
abbrev machine : Machine where
  K := Stack m
  input := inputKey m
  output := outputKey m
  Label := Label m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

def extras (input edges target index row temporary copy rev output : List Bool) : Fin 9 → List Bool :=
  ![input,edges,target,index,row,temporary,copy,rev,output]
def tapes (source : m.K → List Bool) (input edges target index row temporary copy rev output : List Bool) : Stack m → List Bool :=
  Sum.elim source (extras input edges target index row temporary copy rev output)
def config (l : Label m) (source : m.K → List Bool) (input edges target index row temporary copy rev output : List Bool) :=
  cfg l m.initial (tapes m source input edges target index row temporary copy rev output)
def ready (l : Label m) (input edges target index rev output : List Bool) :=
  config m l (fun _ => []) input edges target index [] [] [] rev output
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
