import Holant.Complexity.FixedFieldMachines.PairEncoding
import Holant.Complexity.StackProtocol
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Generic reversal through an actual two-stack symbol-transfer loop. Used to
bridge fixed, already-established little-endian and big-endian component interfaces. -/
namespace Holant.Complexity.FixedFieldMachines
open Turing Computability BinaryCompose StackProtocol

def reverseEncoding {α : Type} (ea : Encoding α Bool) : Encoding α Bool where
  encode a := (ea.encode a).reverse
  decode word := ea.decode word.reverse
  decode_encode a := by simp [ea.decode_encode]

namespace Reverse
abbrev machine : Machine where
  K := Fin 2
  input := 0
  output := 1
  Label := Bool
  main := false
  State := Option Bool × Unit
  initial := (none, ())
  program label := if label then .halt else copyMoveStmt 0 1 false true

def tapes (source destination : List Bool) : Fin 2 → List Bool := ![source, destination]

theorem step_cons (bit : Bool) (source destination : List Bool) :
    machine.computer.step (cfg false () (tapes (bit :: source) destination)) =
      some (cfg false () (tapes source (bit :: destination))) := by
  dsimp [FinTM2.step, TM2.step, machine, cfg, copyMoveStmt, TM2.stepAux, tapes]
  simp only [Bool.cond_true]
  congr 2; funext k; fin_cases k <;> rfl

theorem step_nil (destination : List Bool) :
    machine.computer.step (cfg false () (tapes [] destination)) =
      some (cfg true () (tapes [] destination)) := by
  dsimp [FinTM2.step, TM2.step, machine, cfg, copyMoveStmt, TM2.stepAux, tapes]
  simp only [Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl

theorem move_exact (source destination : List Bool) :
    RunsExactly machine.computer.step (cfg false () (tapes source destination))
      (cfg true () (tapes [] (source.reverse ++ destination))) (source.length + 1) := by
  induction source generalizing destination with
  | nil => simpa using runsExactly_one (step_nil destination)
  | cons bit source ih =>
    have run := (runsExactly_one (step_cons bit source destination)).trans (ih (bit :: destination))
    simpa [List.reverse_cons, List.append_assoc] using run

private theorem init_cfg (word : List Bool) :
    cfg false () (tapes word []) = initList machine.computer word := by
  rw [Machine.init_eq]; congr 1; funext k; fin_cases k <;> rfl

private theorem halt_step (word : List Bool) :
    machine.computer.step (cfg true () (tapes [] word)) = some (haltList machine.computer word) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux]
  congr 2; funext k; fin_cases k <;> rfl

theorem exact_run (word : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer word)
      (haltList machine.computer word.reverse) (word.length + 2) := by
  have first := move_exact word []
  simp only [List.append_nil, init_cfg] at first
  simpa [Nat.add_comm, Nat.add_left_comm] using first.trans (runsExactly_one (halt_step word.reverse))

end Reverse

noncomputable def reverseComputes {α : Type} (ea : Encoding α Bool) :
    Computes ea (reverseEncoding ea) id where
  machine := Reverse.machine
  time := Polynomial.X + 2
  outputs a :=
    { steps := (ea.encode a).length + 2
      evals_in_steps := Reverse.exact_run _
      steps_le_m := by simp }

noncomputable def unreverseComputes {α : Type} (ea : Encoding α Bool) :
    Computes (reverseEncoding ea) ea id where
  machine := Reverse.machine
  time := Polynomial.X + 2
  outputs a :=
    { steps := (ea.encode a).length + 2
      evals_in_steps := by
        change RunsExactly Reverse.machine.computer.step
          (initList Reverse.machine.computer (ea.encode a).reverse)
          (haltList Reverse.machine.computer (ea.encode a)) ((ea.encode a).length + 2)
        simpa only [List.reverse_reverse, List.length_reverse] using Reverse.exact_run (ea.encode a).reverse
      steps_le_m := by simp [reverseEncoding] }

end Holant.Complexity.FixedFieldMachines
