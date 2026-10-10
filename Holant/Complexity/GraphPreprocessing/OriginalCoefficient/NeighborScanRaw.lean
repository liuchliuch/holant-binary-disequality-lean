import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCallRaw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan.Raw
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : RawMachine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

abbrev Stack := NeighborCall.Raw.Stack m ⊕ Fin 5
abbrev Label := NeighborCall.Raw.Label m ⊕ Fin 48
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)

def inputKey : Stack m := .inr 0
def indexKey : Stack m := .inr 1
def holdKey : Stack m := .inr 2
def sideKey : Stack m := .inr 3
def outputKey : Stack m := .inr 4
def tableKey : Stack m := .inl (NeighborCall.Raw.tableKey m)
def targetKey : Stack m := .inl (NeighborCall.Raw.targetKey m)
def endpointKey : Stack m := .inl (NeighborCall.Raw.endpointKey m)
def oppositeKey : Stack m := .inl (NeighborCall.Raw.oppositeKey m)
def temporaryKey : Stack m := .inl (NeighborCall.Raw.temporaryKey m)
def resultKey : Stack m := .inl (.inl m.output)

def returns : NeighborCall.Raw.Label m → Fin 48
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

def program : Label m → Statement m := Returning.program (NeighborCall.Raw.machine m).program (returns m) (outside m)

def machine : RawMachine where
  K := Stack m
  input := inputKey m
  output := outputKey m
  Label := Label m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan.Raw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem erase_scan (m : Machine) : RawMachine.erase (machine m) = Raw.machine (RawMachine.erase m) := by
  unfold RawMachine.erase machine Raw.machine
  congr 1
  funext label
  cases label with
  | inl l => cases l with
    | inl l => rfl
    | inr l => rfl
  | inr l => rfl

abbrev raw : RawMachine := Raw.machine NeighborPredicate.raw

theorem erase_neighbor : RawMachine.erase (machine NeighborPredicate.machine) = raw := by
  rw [erase_scan,NeighborPredicate.erase_machine]

theorem step_eq : HEq raw.view.step (machine NeighborPredicate.machine).computer.step :=
  RawMachine.step_of_erase_eq _ _ erase_neighbor

theorem start_eq : HEq raw.view.start (initList (machine NeighborPredicate.machine).computer) :=
  RawMachine.start_of_erase_eq _ _ erase_neighbor

theorem observer_eq :
    letI : Fintype (machine NeighborPredicate.machine).K := (machine NeighborPredicate.machine).finiteK
    letI : DecidableEq (machine NeighborPredicate.machine).K := (machine NeighborPredicate.machine).decidableK
    HEq raw.view.observeHalt (fun c : (machine NeighborPredicate.machine).Config =>
      (c.stk (machine NeighborPredicate.machine).output,
        decide (∀ k, k ≠ (machine NeighborPredicate.machine).output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_neighbor

def reset : RationalArithmetic.StateCheck raw where
  inspect state := state.1.isNone && NeighborPredicate.reset.inspect state.2
  correct state := by
    rcases state with ⟨flag,state⟩
    cases flag <;> simp [raw,Raw.machine,NeighborPredicate.reset.correct]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
