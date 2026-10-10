import Holant.Complexity.GraphPreprocessing.Frame
import Holant.Complexity.BinaryCompose.Interface
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-! A bundled, uniform finite Boolean-stack realization of ordered frame removal.
The clean full-word instance is a genuine `BinaryCompose.Computes` witness.
The same program's returning contracts retain an arbitrary unconsumed suffix. -/

namespace Holant.Complexity.GraphPreprocessing.Frame
open Turing Computability StackProtocol

/-- Three Boolean stacks, four labels, three scratch states. No natural register. -/
abbrev machine : BinaryCompose.Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 4
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program label := if label = 0 then scanStmt 0 2 0 1 3
    else if label = 1 then copyMoveStmt 2 1 1 2 else .halt

theorem scan_executes : ExecutesAt machine.computer.step (0 : Fin 4)
    (scanStmt 0 2 0 1 3) := by intro state tapes; rfl

theorem restore_executes : ExecutesAt machine.computer.step (1 : Fin 4)
    (copyMoveStmt 2 1 1 2) := by intro state tapes; rfl

def tapes (input output scratch : List Bool) : Fin 3 → List Bool := ![input, output, scratch]

theorem tapes_eq (input output scratch : List Bool) :
    tapes input output scratch = tapes3 (fun _ => []) 0 1 2 input output scratch := by
  funext k
  fin_cases k <;> rfl

/-- Decoder-correct returning extraction with an arbitrary input suffix. -/
theorem machine_extract (input word suffix output : List Bool)
    (h : Holant.Algebraic.unframe input = some (word, suffix)) :
    RunsExactly machine.computer.step (cfg (0 : Fin 4) () (tapes input output []))
      (cfg (2 : Fin 4) () (tapes suffix (word ++ output) [])) (2 * (word.length + 1)) := by
  rw [(unframe_some_iff input word suffix).mp h, tapes_eq, tapes_eq]
  exact extract_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step 0 1 2 3 scan_executes restore_executes () (fun _ => []) word suffix output

/-- Rejecting EOF is operationally separate from accepting an empty frame. -/
theorem machine_reject (input : List Bool) (h : Holant.Algebraic.unframe input = none) :
    ∃ (produced : List Bool) (time : ℕ), time ≤ input.length + 1 ∧ produced.length ≤ input.length ∧
      RunsExactly machine.computer.step (cfg (0 : Fin 4) () (tapes input [] []))
        (cfg (3 : Fin 4) () (tapes [] [] produced.reverse)) time := by
  simpa only [tapes_eq, List.append_nil] using
    rejects (0 : Fin 3) 1 2 (by decide) (by decide) machine.computer.step 0 1 3
      scan_executes () (fun _ => []) input [] [] h

def wordEncoding : Encoding (List Bool) Bool where
  encode := id
  decode := some
  decode_encode _ := rfl

def framedWordEncoding : Encoding (List Bool) Bool where
  encode := Holant.Algebraic.frame
  decode input := (Holant.Algebraic.unframe input).bind
    (fun p => if p.2 = [] then some p.1 else none)
  decode_encode word := by
    have h := Holant.Algebraic.unframe_frame_append word []
    simp only [List.append_nil] at h
    simp [h]

theorem cfg_init (input : List Bool) :
    cfg (0 : Fin 4) () (tapes input [] []) = initList machine.computer input := by
  rw [BinaryCompose.Machine.init_eq]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem halt_step (output : List Bool) :
    machine.computer.step (cfg (2 : Fin 4) () (tapes [] output [])) =
      some (haltList machine.computer output) := by
  rw [BinaryCompose.Machine.halt_eq]
  dsimp [FinTM2.step, TM2.step, cfg, machine, TM2.stepAux]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem full_exact (word : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer (Holant.Algebraic.frame word))
      (haltList machine.computer word) (2 * word.length + 3) := by
  have first := machine_extract (Holant.Algebraic.frame word) word [] [] (by
    simpa using Holant.Algebraic.unframe_frame_append word [])
  simp only [List.append_nil, cfg_init] at first
  have run := first.trans (runsExactly_one (halt_step word))
  convert run using 1 <;> omega

/-- Linear-time clean input/output realization, usable in uniform machine composition. -/
noncomputable def computes : BinaryCompose.Computes framedWordEncoding wordEncoding id where
  machine := machine
  time := Polynomial.X + 2
  outputs word := by
    refine { steps := 2 * word.length + 3
             evals_in_steps := full_exact word
             steps_le_m := ?_ }
    simp [framedWordEncoding, Holant.Algebraic.frame_length]

theorem program_budget (label : Fin 4) : TM2Cost.budget (machine.program label) ≤ 8 := by
  fin_cases label <;> decide

@[simp] theorem stack_count : Fintype.card machine.K = 3 := by decide
@[simp] theorem label_count : Fintype.card machine.Label = 4 := by decide
@[simp] theorem state_count : Fintype.card machine.State = 3 := by decide

end Holant.Complexity.GraphPreprocessing.Frame
