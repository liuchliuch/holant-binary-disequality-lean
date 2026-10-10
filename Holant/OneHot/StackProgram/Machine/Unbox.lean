import Holant.OneHot.StackProgram.Machine.StackWord

/-! Extract the sole final value, check the remaining list terminator and EOF,
and halt with exactly the original raw fieldword and clean work tapes. -/
namespace Holant.OneHot.StackProgram.Machine.Unbox
open Turing Computability Holant.Complexity StackProtocol

abbrev machine : BinaryCompose.Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 6
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program i := if i = 0 then StackWord.markerStmt 0 1 5 5
    else if i = 1 then GraphPreprocessing.Frame.scanStmt 0 2 1 2 5
    else if i = 2 then copyMoveStmt 2 1 2 3
    else if i = 3 then Dispatch.fetchStmt 0 5 4 5
    else .halt

/-- Includes fieldword extraction, singleton check, EOF check and clean halt. -/
theorem run_exact (word : List Bool) :
    RunsExactly machine.computer.step
      (initList machine.computer (true :: Holant.Algebraic.frame word ++ [false]))
      (haltList machine.computer word) (2 * word.length + 5) := by
  have hp := StackWord.pop_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step (0 : Fin 6) 1 2 3 5 5
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) word [false] []
  simp only [List.append_nil, ← GraphPreprocessing.Frame.tapes_eq] at hp
  have checked : machine.computer.step
      (cfg (3 : Fin 6) () (GraphPreprocessing.Frame.tapes [false] word [])) =
      some (cfg (4 : Fin 6) () (GraphPreprocessing.Frame.tapes [] word [])) := by
    simp [machine, FinTM2.step, TM2.step, TM2.stepAux, Dispatch.fetchStmt, cfg,
      GraphPreprocessing.Frame.tapes, Function.update]
    congr 2
    funext k; fin_cases k <;> rfl
  have stopped : machine.computer.step
      (cfg (4 : Fin 6) () (GraphPreprocessing.Frame.tapes [] word [])) =
      some (haltList machine.computer word) := by
    rw [BinaryCompose.Machine.halt_eq]
    change some (⟨none, (none, ()), GraphPreprocessing.Frame.tapes [] word []⟩ : Cfg (Fin 3) (Fin 6) Unit) = _
    congr 2
    funext k; fin_cases k <;> rfl
  rw [BinaryCompose.Machine.init_eq]
  have hinit : BinaryCompose.wordTape (0 : Fin 3) (true :: Holant.Algebraic.frame word ++ [false]) =
      GraphPreprocessing.Frame.tapes (true :: Holant.Algebraic.frame word ++ [false]) [] [] := by
    funext k; fin_cases k <;> rfl
  change RunsExactly _ (cfg (0 : Fin 6) () _) _ _
  rw [hinit]
  convert (hp.trans (runsExactly_one checked)).trans (runsExactly_one stopped) using 1
  omega

/-- The original value encoding is literally the clean final tape. -/
theorem encoded {V : Type} (e : Encoding V Bool) (value : V) :
    RunsExactly machine.computer.step
      (initList machine.computer ((stackEncoding e).encode [value]))
      (haltList machine.computer (e.encode value)) (2 * (e.encode value).length + 5) := by
  simpa only [stackEncoding, framedListEncoding, framedListEncode, List.cons_append] using
    run_exact (e.encode value)

end Holant.OneHot.StackProgram.Machine.Unbox
