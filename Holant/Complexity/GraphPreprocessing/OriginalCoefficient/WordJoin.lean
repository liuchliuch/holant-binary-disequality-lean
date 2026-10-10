import Holant.Complexity.FixedFieldMachines.Wiring
import Holant.Complexity.GraphPreprocessing.Frame
import Holant.Complexity.GraphPreprocessing.FrameMachine

/-! Literal word concatenation from the existing framed-pair protocol. The
first frame is read bitwise and restored directly before the retained suffix. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordJoin
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev machine : Machine where
  K := Fin 3
  input := 0
  output := 0
  Label := Fin 4
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program l := if l=0 then Frame.scanStmt 0 2 0 1 3
    else if l=1 then copyMoveStmt 2 0 1 2 else .halt

def tapes (input scratch : List Bool) : Fin 3 → List Bool := ![input,[],scratch]

theorem initial (input : List Bool) :
    cfg (0 : Fin 4) () (tapes input []) = initList machine.computer input := by
  rw [Machine.init_eq]
  congr 1
  funext k; fin_cases k <;> rfl

theorem halt_step (output : List Bool) :
    machine.computer.step (cfg (2 : Fin 4) () (tapes output [])) = some (haltList machine.computer output) := by
  rw [Machine.halt_eq]
  dsimp [machine,FinTM2.step,TM2.step,TM2.stepAux,cfg]
  congr 2
  funext k; fin_cases k <;> rfl

/-- No operation reads an unbounded word as a register value. -/
theorem exact_run (first second : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer (Holant.Algebraic.frame first ++ second))
      (haltList machine.computer (first++second)) (2*first.length+3) := by
  have a := Frame.scan_exact (0 : Fin 3) 1 2 (by decide) (by decide)
    machine.computer.step (0 : Fin 4) 1 3 (executesAt_tm2 _ _ _ rfl) () (fun _ => []) first second [] []
  have ha (u v : List Bool) : tapes3 (fun _ : Fin 3 => []) 0 1 2 u [] v = tapes u v := by
    funext k; fin_cases k <;> rfl
  rw [ha,ha] at a
  simp only [List.append_nil,initial] at a
  have b := Frame.restore_exact (1 : Fin 3) 0 2 (by decide)
    machine.computer.step (1 : Fin 4) 2 (executesAt_tm2 _ _ _ rfl) () (fun _ => []) [] second first.reverse
  have hb (u v : List Bool) : tapes3 (fun _ : Fin 3 => []) 1 0 2 [] u v = tapes u v := by
    funext k; fin_cases k <;> rfl
  rw [hb,hb] at b
  simp only [List.reverse_reverse,List.length_reverse] at b
  have all := (a.trans b).trans (runsExactly_one (halt_step (first++second)))
  convert all using 1
  omega

noncomputable def computes : Computes (pairEncoding Frame.wordEncoding Frame.wordEncoding)
    Frame.wordEncoding (fun p => p.1++p.2) where
  machine := machine
  time := Polynomial.X+2
  outputs p := {
    steps := 2*p.1.length+3
    evals_in_steps := exact_run p.1 p.2
    steps_le_m := by simp [Frame.wordEncoding] }

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordJoin
