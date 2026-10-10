import Holant.Complexity.FixedFieldMachines.FrameEmit
import Holant.Complexity.GraphPreprocessing.UnaryBinary
import Holant.Complexity.BinaryCompose.OutputBound

/-! Clean finite Boolean-stack frame serialization, composed operationally with
the actual carry-based unary-to-binary converter. This materializes returned
graph coordinate fields in the project's literal framed natural codec. -/
namespace Holant.Complexity.GraphPreprocessing.FrameWriter
open Turing Computability StackProtocol FixedFieldMachines

/-- Any genuine scalar codec can be wrapped in the exact framing convention. -/
def encoding {α : Type} (e : Encoding α Bool) : Encoding α Bool where
  encode a := Holant.Algebraic.frame (e.encode a)
  decode bits := (Holant.Algebraic.unframe bits).bind (fun p =>
    if p.2 = [] then e.decode p.1 else none)
  decode_encode a := by
    have h := Holant.Algebraic.unframe_frame_append (e.encode a) []
    simp only [List.append_nil] at h
    simp [h]

abbrev machine : BinaryCompose.Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 4
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program label := if label = 0 then copyMoveStmt 0 2 0 1
    else if label = 1 then FrameEmit.delimiterStmt 1 2
    else if label = 2 then FrameEmit.emitStmt 2 1 2 3 else .halt

def tapes (source output scratch : List Bool) : Fin 3 → List Bool := ![source, output, scratch]

private theorem at_move : ExecutesAt machine.computer.step (0 : Fin 4) (copyMoveStmt 0 2 0 1) := by intro state tapes; rfl
private theorem at_delimiter : ExecutesAt machine.computer.step (1 : Fin 4) (FrameEmit.delimiterStmt 1 2) := by intro state tapes; rfl
private theorem at_emit : ExecutesAt machine.computer.step (2 : Fin 4) (FrameEmit.emitStmt 2 1 2 3) := by intro state tapes; rfl

/-- Prepared frame emission retains the existing destination suffix. -/
theorem prepend_exact (word suffix : List Bool) :
    RunsExactly machine.computer.step (cfg (0 : Fin 4) () (tapes word suffix []))
      (cfg (3 : Fin 4) () (tapes [] (Holant.Algebraic.frame word ++ suffix) [])) (2 * word.length + 3) := by
  have h := FrameEmit.prepend_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step 0 1 2 3 at_move at_delimiter at_emit () (fun _ => []) word suffix
  convert h using 1 <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem initial_eq (word : List Bool) : cfg (0 : Fin 4) () (tapes word [] []) = initList machine.computer word := by
  rw [BinaryCompose.Machine.init_eq]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem halt_step (word : List Bool) :
    machine.computer.step (cfg (3 : Fin 4) () (tapes [] word [])) = some (haltList machine.computer word) := by
  rw [BinaryCompose.Machine.halt_eq]
  dsimp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem full_exact (word : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer word)
      (haltList machine.computer (Holant.Algebraic.frame word)) (2 * word.length + 4) := by
  have first := prepend_exact word []
  simp only [List.append_nil, initial_eq] at first
  have h := first.trans (runsExactly_one (halt_step (Holant.Algebraic.frame word)))
  convert h using 1
  omega

/-- The finite program is independent of the scalar type and codec. -/
noncomputable def computes {α : Type} (e : Encoding α Bool) : BinaryCompose.Computes e (encoding e) id where
  machine := machine
  time := 2 * Polynomial.X + 4
  outputs a := by
    refine { steps := 2 * (e.encode a).length + 4
             evals_in_steps := full_exact (e.encode a)
             steps_le_m := ?_ }
    simp

/-- A fully compiled pipeline: unary physical coordinate to framed canonical natural.
Intermediate transfer and output growth are charged by `BinaryCompose.andThen`. -/
noncomputable def coordinateComputes :
    BinaryCompose.Computes UnaryBinary.unaryEncoding (encoding encodingNatBool) id := by
  simpa only [Function.comp_id] using UnaryBinary.computes.andThen (computes encodingNatBool)

theorem program_budget (label : Fin 4) : TM2Cost.budget (machine.program label) ≤ 6 := by
  fin_cases label <;> decide

end Holant.Complexity.GraphPreprocessing.FrameWriter
