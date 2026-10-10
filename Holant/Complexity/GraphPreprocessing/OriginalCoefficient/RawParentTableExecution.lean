import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentTable
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentRowExecution
import Holant.Complexity.GraphPreprocessing.Call
import Holant.Complexity.FixedFieldMachines.LeftMap

/-! Physical original-vertex table loop. The executed count package supplies
V unary tokens; each original vertex is queried once in descending order and
its exact row is framed and prepended. One physically emitted list terminator
makes even the empty graph's parent table canonical. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop.Raw
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : RawMachine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Stack := m.K ⊕ Fin 7
abbrev Label := m.Label ⊕ Fin 24
abbrev Memory := Option Bool × m.State
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Memory m)

def rawKey : Stack m := .inr 0
def indexKey : Stack m := .inr 1
def outputKey : Stack m := .inr 2
def temporaryKey : Stack m := .inr 3
def rawCopyKey : Stack m := .inr 4
def verticesKey : Stack m := .inr 5
def inputKey : Stack m := .inr 6

def outside (i : Fin 24) : Statement m := match i.val with
  | 0 => Frame.scanStmt (inputKey m) (temporaryKey m) (.inr 0) (.inr 1) (.inr 23)
  | 1 => copyMoveStmt (temporaryKey m) (rawKey m) (.inr 1) (.inr 2)
  | 2 => Frame.scanStmt (inputKey m) (temporaryKey m) (.inr 2) (.inr 3) (.inr 23)
  | 3 => copyMoveStmt (temporaryKey m) (indexKey m) (.inr 3) (.inr 4)
  | 4 => clearStmt (inputKey m) (.inr 4) (.inr 5)
  | 5 => push (outputKey m) (fun _ => false) (goto (fun _ => .inr 6))
  | 6 => pop (indexKey m) (fun st bit => (bit,st.2))
    (branch (fun st => st.1.isSome)
      (load (fun st => (none,st.2)) (goto (fun _ => .inr 7)))
      (load (fun st => (none,st.2)) (goto (fun _ => .inr 18))))
  | 7 => copyMoveStmt (indexKey m) (temporaryKey m) (.inr 7) (.inr 8)
  | 8 => copyRestoreStmt (indexKey m) (.inl m.input) (temporaryKey m) (.inr 8) (.inr 9)
  | 9 => copyMoveStmt (rawKey m) (temporaryKey m) (.inr 9) (.inr 10)
  | 10 => copyRestoreStmt (rawKey m) (rawCopyKey m) (temporaryKey m) (.inr 10) (.inr 11)
  | 11 => copyMoveStmt (rawCopyKey m) (temporaryKey m) (.inr 11) (.inr 12)
  | 12 => FrameEmit.delimiterStmt (.inl m.input) (.inr 13)
  | 13 => FrameEmit.emitStmt (temporaryKey m) (.inl m.input) (.inr 13) (.inl m.main)
  | 14 => copyMoveStmt (.inl m.output) (temporaryKey m) (.inr 14) (.inr 15)
  | 15 => FrameEmit.delimiterStmt (outputKey m) (.inr 16)
  | 16 => FrameEmit.emitStmt (temporaryKey m) (outputKey m) (.inr 16) (.inr 17)
  | 17 => push (outputKey m) (fun _ => true) (goto (fun _ => .inr 6))
  | 18 => clearStmt (rawKey m) (.inr 18) (.inr 22)
  | 23 => load (fun _ => (some false,m.initial)) .halt
  | _ => .halt

def states : StateEmbedding m.State (Memory m) where
  put state := (none,state)
  get := Prod.snd
  get_put _ := rfl

def program : Label m → Statement m
  | .inl l => Call.statement (states m) Sum.inl (some (.inr (14 : Fin 24))) (m.program l)
  | .inr i => outside m i

def machine : RawMachine where
  K := Stack m
  input := inputKey m
  output := outputKey m
  Label := Label m
  main := .inr 0
  State := Memory m
  initial := (none,m.initial)
  program := program m

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop.Raw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

/-- Literal equality of programs, keys, initial state and halt behavior. -/
theorem erase_loop (m : Machine) : RawMachine.erase (machine m) = Raw.machine (RawMachine.erase m) := by
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

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentTable
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev raw : RawMachine := (RawMachine.erase CountsPackage.machine).compose (ParentTableLoop.Raw.machine RawParentRow.raw)

theorem erase_machine : RawMachine.erase machine = raw := by
  change RawMachine.erase (CountsPackage.machine.compose (ParentTableLoop.machine RawParentRow.machine)) = _
  rw [RawMachine.erase_compose,ParentTableLoop.erase_loop,RawParentRow.erase_machine]

theorem step_eq : HEq raw.view.step machine.computer.step := RawMachine.step_of_erase_eq _ _ erase_machine
theorem start_eq : HEq raw.view.start (initList machine.computer) := RawMachine.start_of_erase_eq _ _ erase_machine
theorem observer_eq :
    letI : Fintype machine.K := machine.finiteK
    letI : DecidableEq machine.K := machine.decidableK
    HEq raw.view.observeHalt (fun c : machine.Config =>
      (c.stk machine.output,decide (∀ k, k ≠ machine.output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_machine

def countsCheck : RationalArithmetic.StateCheck (RawMachine.erase CountsPackage.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def reset : RationalArithmetic.StateCheck raw := countsCheck.compose (ParentTableLoop.rawCheck RawParentRow.reset)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentTable
