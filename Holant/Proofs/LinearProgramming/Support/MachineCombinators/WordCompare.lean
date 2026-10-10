import Holant.Proofs.LinearProgramming.Support.MachineCombinators.WordEqual
import Holant.Complexity.GraphPreprocessing.FrameMachine
import Holant.Complexity.FixedFieldMachines.PairEncoding

/-! A clean Boolean result for a real bitwise word comparison. The only input
framing is the established pair codec, and every bit and EOF test is charged. -/
open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WordCompare
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Memory := WordEqual.Memory Unit
abbrev Statement := TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 5) Memory

def program (label : Fin 5) : Statement := match label.val with
  | 0 => Frame.scanStmt 0 2 0 1 4
  | 1 => copyMoveStmt 2 1 1 2
  | 2 => WordEqual.statement 1 0 2 3 3
  | 3 => push 0 (fun v => v.2.1) (load (fun _ => WordEqual.clean true ()) .halt)
  | _ => load (fun _ => (some false,(true,none,()))) .halt

abbrev machine : Machine where
  K := Fin 3
  input := 0
  output := 0
  Label := Fin 5
  main := 0
  State := Memory
  initial := WordEqual.clean true ()
  program := program

def work (input left temporary : List Bool) : Fin 3 → List Bool := ![input,left,temporary]
def config (label : Fin 5) (same : Bool) (input left temporary : List Bool) : machine.Config :=
  WordEqual.cfg label same () (work input left temporary)

@[simp] theorem update_input (input left temporary word : List Bool) :
    Function.update (work input left temporary) 0 word = work word left temporary := by
  funext k; fin_cases k <;> simp [work,Function.update]
@[simp] theorem update_left (input left temporary word : List Bool) :
    Function.update (work input left temporary) 1 word = work input word temporary := by
  funext k; fin_cases k <;> simp [work,Function.update]
@[simp] theorem update_temporary (input left temporary word : List Bool) :
    Function.update (work input left temporary) 2 word = work input left word := by
  funext k; fin_cases k <;> simp [work,Function.update]

theorem parse_left (a b : List Bool) :
    RunsExactly (TM2.step program) (config 0 true (Holant.Algebraic.frame a ++ b) [] [])
      (config 2 true b a []) (2*(a.length+1)) := by
  have h := Frame.extract_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    (TM2.step program) 0 1 2 4 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    (true,none,()) (work [] [] []) a b []
  simpa only [config,WordEqual.cfg,WordEqual.clean,cfg,tapes3,update_input,update_left,
    update_temporary,List.append_nil] using h

theorem compare (a b : List Bool) :
    RunsExactly (TM2.step program) (config 2 true b a [])
      (config 3 (decide (a=b)) [] [] []) (max a.length b.length+1) := by
  have h := WordEqual.compare_exact (1 : Fin 3) 0 (by decide) (TM2.step program) 2 3 3
    (by intro state tapes; rfl) true () (work [] [] []) a b
  simpa [WordEqual.Runs,RunsExactly,WordEqual.tapes2,config,update_left,update_input] using h

theorem work_empty : work [] [] [] = fun _ => [] := by funext k; fin_cases k <;> rfl
theorem initial (input : List Bool) : initList machine.computer input = config 0 true input [] [] := by
  rw [Machine.init_eq]
  have h := update_input [] [] [] input
  rw [work_empty] at h
  change wordTape (0 : Fin 3) input = _ at h
  change (⟨some 0,WordEqual.clean true (),wordTape (0 : Fin 3) input⟩ : machine.Config) = _
  rw [h]; rfl

theorem finish (same : Bool) : TM2.step program (config 3 same [] [] []) =
    some (haltList machine.computer [same]) := by
  rw [Machine.halt_eq]
  have h := update_input [] [] [] [same]
  rw [work_empty] at h
  change some (⟨none,WordEqual.clean true (),Function.update (work [] [] []) 0 [same]⟩ : machine.Config) = _
  rw [update_input]
  rw [← h]; rfl

def inputEncoding := FixedFieldMachines.pairEncoding Frame.wordEncoding Frame.wordEncoding
def value (x : List Bool × List Bool) : Bool := decide (x.1=x.2)
def ticks (x : List Bool × List Bool) : ℕ := 2*x.1.length+max x.1.length x.2.length+4

theorem exact_run (x : List Bool × List Bool) :
    RunsExactly machine.computer.step (initList machine.computer (inputEncoding.encode x))
      (haltList machine.computer (encodingBoolBool.encode (value x))) (ticks x) := by
  rw [initial]
  have all := ((parse_left x.1 x.2).trans (compare x.1 x.2)).trans
    (runsExactly_one (finish (decide (x.1=x.2))))
  have ht : ticks x = 1+((max x.1.length x.2.length+1)+2*(x.1.length+1)) := by unfold ticks; omega
  rw [ht]
  exact all

theorem ticks_le (x : List Bool × List Bool) : ticks x ≤ 2*(inputEncoding.encode x).length+2 := by
  simp only [ticks,inputEncoding,FixedFieldMachines.pairEncoding,Frame.wordEncoding,
    List.length_append,Holant.Algebraic.frame_length,id_eq]
  omega

noncomputable def computes : Computes inputEncoding encodingBoolBool value where
  machine := machine
  time := 2*Polynomial.X+2
  outputs x := {
    steps := ticks x
    evals_in_steps := exact_run x
    steps_le_m := by simpa using ticks_le x }

theorem inFP : InFP inputEncoding encodingBoolBool value := computes.inFP
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WordCompare
