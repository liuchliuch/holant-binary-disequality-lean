import Holant.Complexity.FixedFieldMachines.PairEncoding
import Holant.Complexity.FixedFieldMachines.FrameEmit
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Actual clean finite Boolean-stack wiring machines. All copying, discarding,
parsing and framing is charged by exact execution theorems. -/
namespace Holant.Complexity.FixedFieldMachines.Wiring
open Turing Computability BinaryCompose StackProtocol
open Holant.Algebraic

abbrev Keys := Fin 3
abbrev Labels := Fin 7

def tapes (a b c : List Bool) : Keys → List Bool := ![a, b, c]

theorem tapes012 (a b c : List Bool) : tapes a b c = tapes3 (fun _ => []) 0 1 2 a b c := by
  funext k; fin_cases k <;> rfl

theorem tapes102 (a b c : List Bool) : tapes a b c = tapes3 (fun _ => []) 1 0 2 b a c := by
  funext k; fin_cases k <;> rfl

/-- Swap `frame a ++ b` into `frame b ++ a`. -/
abbrev swapMachine : Machine where
  K := Keys
  input := 0
  output := 1
  Label := Labels
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program l := if l = 0 then GraphPreprocessing.Frame.scanStmt 0 2 0 1 6
    else if l = 1 then copyMoveStmt 2 1 1 2
    else if l = 2 then copyMoveStmt 0 2 2 3
    else if l = 3 then FrameEmit.delimiterStmt 1 4
    else if l = 4 then FrameEmit.emitStmt 2 1 4 5 else .halt


private theorem swap_init (word : List Bool) :
    cfg (0 : Labels) () (tapes word [] []) = initList swapMachine.computer word := by
  rw [Machine.init_eq]; congr 1; funext k; fin_cases k <;> rfl

private theorem swap_halt (word : List Bool) :
    swapMachine.computer.step (cfg (5 : Labels) () (tapes [] word [])) =
      some (haltList swapMachine.computer word) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step, TM2.step, swapMachine, cfg, TM2.stepAux]
  congr 2; funext k; fin_cases k <;> rfl

theorem swap_exact (a b : List Bool) :
    RunsExactly swapMachine.computer.step (initList swapMachine.computer (frame a ++ b))
      (haltList swapMachine.computer (frame b ++ a)) (2 * a.length + 2 * b.length + 6) := by
  have first := GraphPreprocessing.Frame.extract_exact (0 : Keys) 1 2
    (by decide) (by decide) (by decide) swapMachine.computer.step (0 : Labels) 1 2 6
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (fun _ => []) a b []
  rw [← tapes012, ← tapes012] at first
  simp only [List.append_nil, swap_init] at first
  have last := FrameEmit.prepend_exact (0 : Keys) 1 2
    (by decide) (by decide) (by decide) swapMachine.computer.step (2 : Labels) 3 4 5
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) b a
  rw [← tapes012, ← tapes012] at last
  have run := (first.trans last).trans (runsExactly_one (swap_halt (frame b ++ a)))
  convert run using 1; omega

noncomputable def swapComputes {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool) :
    Computes (pairEncoding ea eb) (pairEncoding eb ea) Prod.swap where
  machine := swapMachine
  time := 2 * Polynomial.X + 6
  outputs p :=
    { steps := 2 * (ea.encode p.1).length + 2 * (eb.encode p.2).length + 6
      evals_in_steps := swap_exact _ _
      steps_le_m := by simp; omega }

/-- Duplicate a word, then consume one copy to emit a framed prefix. -/
abbrev diagonalMachine : Machine where
  K := Keys
  input := 0
  output := 1
  Label := Labels
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program l := if l = 0 then copyMoveStmt 0 2 0 1
    else if l = 1 then copyRestoreStmt 0 1 2 1 2
    else if l = 2 then copyMoveStmt 0 2 2 3
    else if l = 3 then FrameEmit.delimiterStmt 1 4
    else if l = 4 then FrameEmit.emitStmt 2 1 4 5 else .halt

private theorem diagonal_init (word : List Bool) :
    cfg (0 : Labels) () (tapes word [] []) = initList diagonalMachine.computer word := by
  rw [Machine.init_eq]; congr 1; funext k; fin_cases k <;> rfl

private theorem diagonal_halt (word : List Bool) :
    diagonalMachine.computer.step (cfg (5 : Labels) () (tapes [] word [])) =
      some (haltList diagonalMachine.computer word) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step, TM2.step, diagonalMachine, cfg, TM2.stepAux]
  congr 2; funext k; fin_cases k <;> rfl

theorem diagonal_exact (word : List Bool) :
    RunsExactly diagonalMachine.computer.step (initList diagonalMachine.computer word)
      (haltList diagonalMachine.computer (frame word ++ word)) (4 * word.length + 6) := by
  have first := copy_exact_frame (0 : Keys) 1 2
    (by decide) (by decide) (by decide) diagonalMachine.computer.step (0 : Labels) 1 2
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (fun _ => []) word []
  rw [← tapes012, ← tapes012] at first
  simp only [List.append_nil, diagonal_init] at first
  have last := FrameEmit.prepend_exact (0 : Keys) 1 2
    (by decide) (by decide) (by decide) diagonalMachine.computer.step (2 : Labels) 3 4 5
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) word word
  rw [← tapes012, ← tapes012] at last
  have run := (first.trans last).trans (runsExactly_one (diagonal_halt (frame word ++ word)))
  convert run using 1; omega

noncomputable def diagonalComputes {α : Type} (ea : Encoding α Bool) :
    Computes ea (pairEncoding ea ea) (fun a => (a, a)) where
  machine := diagonalMachine
  time := 4 * Polynomial.X + 6
  outputs a :=
    { steps := 4 * (ea.encode a).length + 6
      evals_in_steps := diagonal_exact _
      steps_le_m := by simp }

/-- Extract the first word and erase the complete second word. -/
abbrev firstMachine : Machine where
  K := Keys
  input := 0
  output := 1
  Label := Labels
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program l := if l = 0 then GraphPreprocessing.Frame.scanStmt 0 2 0 1 6
    else if l = 1 then copyMoveStmt 2 1 1 2
    else if l = 2 then clearStmt 0 2 3 else .halt

private theorem first_init (word : List Bool) :
    cfg (0 : Labels) () (tapes word [] []) = initList firstMachine.computer word := by
  rw [Machine.init_eq]; congr 1; funext k; fin_cases k <;> rfl

private theorem first_halt (word : List Bool) :
    firstMachine.computer.step (cfg (3 : Labels) () (tapes [] word [])) =
      some (haltList firstMachine.computer word) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step, TM2.step, firstMachine, cfg, TM2.stepAux]
  congr 2; funext k; fin_cases k <;> rfl

theorem first_exact (a b : List Bool) :
    RunsExactly firstMachine.computer.step (initList firstMachine.computer (frame a ++ b))
      (haltList firstMachine.computer a) (2 * a.length + b.length + 4) := by
  have first := GraphPreprocessing.Frame.extract_exact (0 : Keys) 1 2
    (by decide) (by decide) (by decide) firstMachine.computer.step (0 : Labels) 1 2 6
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (fun _ => []) a b []
  rw [← tapes012, ← tapes012] at first
  simp only [List.append_nil, first_init] at first
  have last := clear_exact firstMachine.computer.step (0 : Keys) (2 : Labels) 3
    (executesAt_tm2 _ _ _ rfl) () (tapes b a [])
  have hu : Function.update (tapes b a []) (0 : Keys) [] = tapes [] a [] := by
    funext k; fin_cases k <;> rfl
  simp only [hu] at last
  change RunsExactly _ _ _ (b.length + 1) at last
  have run := (first.trans last).trans (runsExactly_one (first_halt a))
  convert run using 1; omega

noncomputable def firstComputes {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool) :
    Computes (pairEncoding ea eb) ea Prod.fst where
  machine := firstMachine
  time := Polynomial.X + 3
  outputs p :=
    { steps := 2 * (ea.encode p.1).length + (eb.encode p.2).length + 4
      evals_in_steps := first_exact _ _
      steps_le_m := by simp; omega }

/-- Second projection is a composed finite swapping/parsing/erasing program. -/
noncomputable def secondComputes {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool) :
    Computes (pairEncoding ea eb) eb Prod.snd :=
  congrComputes ((swapComputes ea eb).andThen (firstComputes eb ea)) (fun _ => rfl)

end Holant.Complexity.FixedFieldMachines.Wiring
