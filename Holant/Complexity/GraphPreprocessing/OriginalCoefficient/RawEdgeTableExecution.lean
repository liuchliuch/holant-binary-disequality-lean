import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawEdgeTable
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWordRaw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop.Raw
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (r : RawMachine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev Stack := r.K ⊕ Fin 7
abbrev Label := r.Label ⊕ Fin 24
abbrev Memory := Option Bool × r.State
abbrev Statement := TM2.Stmt (fun _ : Stack r => Bool) (Label r) (Memory r)

def rawKey : Stack r := .inr 0
def indexKey : Stack r := .inr 1
def outputKey : Stack r := .inr 2
def temporaryKey : Stack r := .inr 3
def rawCopyKey : Stack r := .inr 4
def verticesKey : Stack r := .inr 5
def inputKey : Stack r := .inr 6

def states : StateEmbedding r.State (Memory r) where
  put state := (none,state)
  get := Prod.snd
  get_put _ := rfl

def outside (i : Fin 24) : Statement r := match i.val with
  | 0 => Frame.scanStmt (inputKey r) (temporaryKey r) (.inr 0) (.inr 1) (.inr 23)
  | 1 => copyMoveStmt (temporaryKey r) (rawKey r) (.inr 1) (.inr 2)
  | 2 => Frame.scanStmt (inputKey r) (temporaryKey r) (.inr 2) (.inr 3) (.inr 23)
  | 3 => copyMoveStmt (temporaryKey r) (verticesKey r) (.inr 3) (.inr 4)
  | 4 => copyMoveStmt (inputKey r) (temporaryKey r) (.inr 4) (.inr 5)
  | 5 => copyMoveStmt (temporaryKey r) (indexKey r) (.inr 5) (.inr 6)
  | 6 => pop (indexKey r) (fun st bit => (bit,st.2))
    (branch (fun st => st.1.isSome)
      (load (fun st => (none,st.2)) (goto (fun _ => .inr 7)))
      (load (fun st => (none,st.2)) (goto (fun _ => .inr 18))))
  | 7 => copyMoveStmt (indexKey r) (temporaryKey r) (.inr 7) (.inr 8)
  | 8 => copyRestoreStmt (indexKey r) (.inl r.input) (temporaryKey r) (.inr 8) (.inr 9)
  | 9 => copyMoveStmt (rawKey r) (temporaryKey r) (.inr 9) (.inr 10)
  | 10 => copyRestoreStmt (rawKey r) (rawCopyKey r) (temporaryKey r) (.inr 10) (.inr 11)
  | 11 => copyMoveStmt (rawCopyKey r) (temporaryKey r) (.inr 11) (.inr 12)
  | 12 => FrameEmit.delimiterStmt (.inl r.input) (.inr 13)
  | 13 => FrameEmit.emitStmt (temporaryKey r) (.inl r.input) (.inr 13) (.inl r.main)
  | 14 => copyMoveStmt (.inl r.output) (temporaryKey r) (.inr 14) (.inr 15)
  | 15 => copyMoveStmt (temporaryKey r) (outputKey r) (.inr 15) (.inr 6)
  | 18 => clearStmt (rawKey r) (.inr 18) (.inr 19)
  | 19 => copyMoveStmt (verticesKey r) (temporaryKey r) (.inr 19) (.inr 20)
  | 20 => FrameEmit.delimiterStmt (outputKey r) (.inr 21)
  | 21 => FrameEmit.emitStmt (temporaryKey r) (outputKey r) (.inr 21) (.inr 22)
  | 23 => load (fun _ => (some false,r.initial)) .halt
  | _ => .halt


def program : Label r → Statement r
  | .inl l => Call.statement (states r) Sum.inl (some (.inr (14 : Fin 24))) (r.program l)
  | .inr i => outside r i

def machine : RawMachine where
  K := Stack r
  input := inputKey r
  output := outputKey r
  Label := Label r
  main := .inr 0
  State := Memory r
  initial := (none,r.initial)
  program := program r

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop.Raw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
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

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawEdgeTable
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev raw : RawMachine := (RawMachine.erase CountsPackage.machine).compose (EdgeTableLoop.Raw.machine EdgeWord.raw)

theorem erase_machine : RawMachine.erase machine = raw := by
  change RawMachine.erase (CountsPackage.machine.compose (EdgeTableLoop.machine EdgeWord.machine)) = _
  rw [RawMachine.erase_compose,EdgeTableLoop.erase_loop,EdgeWord.erase_machine]

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
def reset : RationalArithmetic.StateCheck raw := countsCheck.compose (EdgeTableLoop.rawCheck EdgeWord.reset)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawEdgeTable
