import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildPredicateExecution
import Holant.Complexity.GraphPreprocessing.Call

/-! Original-order child filtering. Actual row frames are consumed once, a
physical unary counter tracks their original positions, and every row invokes
the finite child predicate. Matched IDs are emitted in reversed bit order and
one final physical reversal restores increasing original vertex order. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate.Raw
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : RawMachine)
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

def states : StateEmbedding m.State (Option Bool × m.State) where
  put state := (none,state)
  get := Prod.snd
  get_put _ := rfl

def program : Label m → Statement m
  | .inl l => Call.statement (states m) Sum.inl (some (.inr (19 : Fin 48))) (m.program l)
  | .inr l => outside m l
def machine : RawMachine where
  K := Stack m
  input := inputKey m
  output := outputKey m
  Label := Label m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate.Raw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

theorem erase_scanner (m : Machine) : RawMachine.erase (machine m)=Raw.machine (RawMachine.erase m) := by
  unfold RawMachine.erase machine Raw.machine
  congr 1
  funext label
  cases label <;> rfl
abbrev raw : RawMachine := Raw.machine ChildPredicate.raw
theorem erase_actual : RawMachine.erase (machine actual)=raw := by rw [erase_scanner,ChildPredicate.erase_machine]
theorem step_eq : HEq raw.view.step (machine actual).computer.step := RawMachine.step_of_erase_eq _ _ erase_actual
theorem start_eq : HEq raw.view.start (initList (machine actual).computer) := RawMachine.start_of_erase_eq _ _ erase_actual
theorem observer_eq :
    letI : Fintype (machine actual).K := (machine actual).finiteK
    letI : DecidableEq (machine actual).K := (machine actual).decidableK
    HEq raw.view.observeHalt (fun c : (machine actual).Config =>
      (c.stk (machine actual).output,decide (∀ k, k ≠ (machine actual).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_actual

def reset : RationalArithmetic.StateCheck raw where
  inspect state := state.1.isNone && ChildPredicate.reset.inspect state.2
  correct state := by
    rcases state with ⟨flag,state⟩
    cases flag <;> simp [raw,Raw.machine,ChildPredicate.reset.correct]
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
