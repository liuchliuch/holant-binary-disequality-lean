import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.FirstTrue
import Holant.Complexity.FixedFieldMachines.LeftMap
import Holant.Complexity.GraphPreprocessing.Call

/-! A physical framed Boolean selects the root case or a real parent machine.
The root case erases its input and emits depth zero / no parent. The nonroot
case copies the actual input into the provider and returns its clean word. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCase
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

abbrev Stack := m.K ⊕ Fin 3
abbrev Label := m.Label ⊕ Fin 16
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)
def phase (i : Fin 16) : Label m := .inr i
def inputKey : Stack m := .inr 0
def temporaryKey : Stack m := .inr 1
def outputKey : Stack m := .inr 2

def outside (i : Fin 16) : Statement m := match i.val with
  | 0 => Frame.scanStmt (inputKey m) (temporaryKey m) (phase m 0) (phase m 1) (phase m 15)
  | 1 => copyMoveStmt (temporaryKey m) (outputKey m) (phase m 1) (phase m 2)
  | 2 => pop (outputKey m) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun v => (none,v.2)) (goto (fun _ => phase m 8)))
        (load (fun v => (none,v.2)) (goto (fun _ => phase m 3))))
      (load (fun v => (none,v.2)) (goto (fun _ => phase m 15))))
  | 3 => copyMoveStmt (inputKey m) (temporaryKey m) (phase m 3) (phase m 4)
  | 4 => copyMoveStmt (temporaryKey m) (.inl m.input) (phase m 4) (.inl m.main)
  | 5 => copyMoveStmt (.inl m.output) (temporaryKey m) (phase m 5) (phase m 6)
  | 6 => copyMoveStmt (temporaryKey m) (outputKey m) (phase m 6) (phase m 7)
  | 8 => clearStmt (inputKey m) (phase m 8) (phase m 9)
  | 9 => push (outputKey m) (fun _ => false) (push (outputKey m) (fun _ => false) (goto (fun _ => phase m 7)))
  | 15 => load (fun _ => (some false,m.initial)) .halt
  | _ => .halt

def program : Label m → Statement m
  | .inl l => Call.statement (LeftMap.states m) Sum.inl (some (phase m 5)) (m.program l)
  | .inr l => outside m l
abbrev machine : Machine where
  K := Stack m
  input := inputKey m
  output := outputKey m
  Label := Label m
  main := phase m 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

def extras (input temporary output : List Bool) : Fin 3 → List Bool := ![input,temporary,output]
def tapes (source : m.K → List Bool) (input temporary output : List Bool) : Stack m → List Bool :=
  Sum.elim source (extras input temporary output)
def config (l : Label m) (source : m.K → List Bool) (input temporary output : List Bool) :=
  cfg l m.initial (tapes m source input temporary output)
def ready (l : Label m) (input temporary output : List Bool) := config m l (fun _ => []) input temporary output

@[simp] theorem update_input (source : m.K → List Bool) (input temporary output word : List Bool) :
    Function.update (tapes m source input temporary output) (inputKey m) word=tapes m source word temporary output := by
  funext k; cases k with
  | inl k => simp [tapes,inputKey]
  | inr k => fin_cases k <;> simp [tapes,extras,inputKey,Function.update]
@[simp] theorem update_temporary (source : m.K → List Bool) (input temporary output word : List Bool) :
    Function.update (tapes m source input temporary output) (temporaryKey m) word=tapes m source input word output := by
  funext k; cases k with
  | inl k => simp [tapes,temporaryKey]
  | inr k => fin_cases k <;> simp [tapes,extras,temporaryKey,Function.update]
@[simp] theorem update_output (source : m.K → List Bool) (input temporary output word : List Bool) :
    Function.update (tapes m source input temporary output) (outputKey m) word=tapes m source input temporary word := by
  funext k; cases k with
  | inl k => simp [tapes,outputKey]
  | inr k => fin_cases k <;> simp [tapes,extras,outputKey,Function.update]
@[simp] theorem update_source (source : m.K → List Bool) (input temporary output : List Bool) (k : m.K) (word : List Bool) :
    Function.update (tapes m source input temporary output) (.inl k) word=
      tapes m (Function.update source k word) input temporary output := MachineFrame.update_left source _ k word

theorem tapes_empty : tapes m (fun _ => []) [] [] [] = fun _ => [] := by
  funext k; cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem initial (input : List Bool) : initList (machine m).computer input = ready m (phase m 0) input [] [] := by
  rw [Machine.init_eq]
  have h := update_input m (fun _ => []) [] [] [] input
  rw [tapes_empty] at h
  change wordTape (inputKey m) input = _ at h
  change (⟨some (phase m 0),(none,m.initial),wordTape (inputKey m) input⟩ : (machine m).Config) = _
  rw [h]; rfl

theorem halt_step (output : List Bool) : TM2.step (program m) (ready m (phase m 7) [] [] output) =
    some (haltList (machine m).computer output) := by
  rw [Machine.halt_eq]
  have h := update_output m (fun _ => []) [] [] [] output
  rw [tapes_empty] at h
  change wordTape (outputKey m) output = _ at h
  change some (⟨none,(none,m.initial),tapes m (fun _ => []) [] [] output⟩ : (machine m).Config) = _
  rw [←h]

theorem parse_flag (bit : Bool) (input : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (phase m 0) (Holant.Algebraic.frame [bit]++input) [] [])
      (ready m (phase m 2) input [] [bit]) 4 := by
  have h := Frame.extract_exact (inputKey m) (outputKey m) (temporaryKey m)
    (by simp [inputKey,outputKey]) (by simp [inputKey,temporaryKey]) (by simp [outputKey,temporaryKey])
    (TM2.step (program m)) (phase m 0) (phase m 1) (phase m 2) (phase m 15)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] []) [bit] input []
  simpa [ready,config,tapes3,update_input,update_output,update_temporary] using h

theorem read_flag (bit : Bool) (input : List Bool) :
    TM2.step (program m) (ready m (phase m 2) input [] [bit]) =
      some (ready m (phase m (if bit then 8 else 3)) input [] []) := by
  cases bit <;>
    change some (⟨some _,(none,m.initial),Function.update (tapes m (fun _ => []) input [] [_]) (outputKey m) []⟩ : (machine m).Config) = _
  all_goals rw [update_output]; rfl

theorem root_exact (input : List Bool) :
    RunsExactly (machine m).computer.step
      (initList (machine m).computer (Holant.Algebraic.frame [true]++input))
      (haltList (machine m).computer [false,false]) (input.length+8) := by
  have clear := clear_exact (TM2.step (program m)) (inputKey m) (phase m 8) (phase m 9)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) input [] [])
  rw [update_input] at clear
  have emit : TM2.step (program m) (ready m (phase m 9) [] [] []) = some (ready m (phase m 7) [] [] [false,false]) := by
    change some (⟨some _,(none,m.initial),Function.update (Function.update (tapes m (fun _ => []) [] [] []) (outputKey m) [false])
      (outputKey m) [false,false]⟩ : (machine m).Config) = _
    rw [update_output,update_output]; rfl
  have all := ((((parse_flag m true input).trans (runsExactly_one (read_flag m true input))).trans clear).trans
    (runsExactly_one emit)).trans (runsExactly_one (halt_step m [false,false]))
  rw [initial]
  change RunsExactly (TM2.step (program m)) _ _ _
  convert all using 1 <;> first | rfl | (change _=1+(1+((input.length+1)+(1+4))); omega)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCase
