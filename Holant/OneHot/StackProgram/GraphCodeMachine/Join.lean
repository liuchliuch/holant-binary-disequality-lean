import Holant.OneHot.StackProgram.GraphCodeMachine.Actions
import Holant.Complexity.FixedFieldMachines.PairEncoding
import Holant.Complexity.BinaryCompose.OutputBound

/-! Physical concatenation of two serialized bytecode chunks and a fixed suffix.
The input chunk bytes retain every finite label literally. Only their final list
terminators are checked and removed; no coefficient value is decoded or searched. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine.Join
open Turing Computability Holant.Complexity StackProtocol
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false

def terminator (src : Fin 4) (next : Fin 11) : Stmt (Fin 4) (Fin 11) Unit :=
  pop src (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
    (branch (fun v => v.1.getD false)
      (load (fun v => (none, v.2)) (goto (fun _ => 10)))
      (load (fun v => (none, v.2)) (goto (fun _ => next))))
    (load (fun v => (none, v.2)) (goto (fun _ => 10))))

abbrev machine (suffix : List Bool) : BinaryCompose.Machine where
  K := Fin 4
  input := 0
  output := 0
  Label := Fin 11
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program phase :=
    if phase = 0 then GraphPreprocessing.Frame.scanStmt 0 2 0 1 10
    else if phase = 1 then copyMoveStmt 2 1 1 2
    else if phase = 2 then copyMoveStmt 0 3 2 3
    else if phase = 3 then terminator 3 4
    else if phase = 4 then FixedFieldMachines.Constant.pushWord 0 suffix (goto (fun _ => 5))
    else if phase = 5 then copyMoveStmt 3 0 5 6
    else if phase = 6 then copyMoveStmt 1 2 6 7
    else if phase = 7 then terminator 2 8
    else if phase = 8 then copyMoveStmt 2 0 8 9
    else .halt

def tapes (input left temporary right : List Bool) : Fin 4 → List Bool :=
  ![input, left, temporary, right]

theorem reject_halts (suffix : List Bool) (work : Fin 4 → List Bool) :
    (machine suffix).computer.step (cfg (10 : Fin 11) () work) =
      some (⟨none, (none, ()), work⟩ : Cfg (Fin 4) (Fin 11) Unit) := rfl

/-- Exact clean execution, including the outer frame, checked terminators,
reversals, fixed suffix loader and final halt. -/
theorem run_exact (suffix p q : List Bool) :
    RunsExactly (machine suffix).computer.step
      (initList (machine suffix).computer (Holant.Algebraic.frame (p ++ [false]) ++ (q ++ [false])))
      (haltList (machine suffix).computer (p ++ q ++ suffix)) (4 * p.length + 2 * q.length + 14) := by
  have extracted := GraphPreprocessing.Frame.extract_exact (0 : Fin 4) 1 2
    (by decide) (by decide) (by decide) (machine suffix).computer.step (0 : Fin 11) 1 2 10
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) (p ++ [false]) (q ++ [false]) []
  have first : RunsExactly (machine suffix).computer.step
      (cfg (0 : Fin 11) () (tapes (Holant.Algebraic.frame (p ++ [false]) ++ (q ++ [false])) [] [] []))
      (cfg (2 : Fin 11) () (tapes (q ++ [false]) (p ++ [false]) [] [])) (2 * p.length + 4) := by
    convert extracted using 1 <;> try { unfold cfg; congr 1; funext k; fin_cases k }
    all_goals simp [cfg, tapes3, tapes, Nat.mul_add]
    all_goals funext k; fin_cases k <;> rfl
  have movedQ := copy_move_exact (0 : Fin 4) 2 3 (by decide) (by decide)
    (machine suffix).computer.step (2 : Fin 11) 3 (executesAt_tm2 _ _ _ rfl)
    () (tapes [] (p ++ [false]) [] []) (q ++ [false]) [] []
  have reverseQ : RunsExactly (machine suffix).computer.step
      (cfg (2 : Fin 11) () (tapes (q ++ [false]) (p ++ [false]) [] []))
      (cfg (3 : Fin 11) () (tapes [] (p ++ [false]) [] (false :: q.reverse))) (q.length + 2) := by
    convert movedQ using 1 <;> try { unfold cfg; congr 1; funext k; fin_cases k }
    all_goals simp [cfg, tapes3, tapes]
    all_goals funext k; fin_cases k <;> rfl
  have removeQ : (machine suffix).computer.step
      (cfg (3 : Fin 11) () (tapes [] (p ++ [false]) [] (false :: q.reverse))) =
      some (cfg (4 : Fin 11) () (tapes [] (p ++ [false]) [] q.reverse)) := by
    simp [machine, FinTM2.step, TM2.step, terminator, TM2.stepAux, cfg, tapes]
    funext k; fin_cases k <;> rfl
  have load : (machine suffix).computer.step
      (cfg (4 : Fin 11) () (tapes [] (p ++ [false]) [] q.reverse)) =
      some (cfg (5 : Fin 11) () (tapes suffix (p ++ [false]) [] q.reverse)) := by
    change some (TM2.stepAux (FixedFieldMachines.Constant.pushWord 0 suffix (goto (fun _ => (5 : Fin 11))))
      (none, ()) _) = _
    rw [FixedFieldMachines.Constant.pushWord_eval]
    simp [TM2.stepAux, cfg, tapes]
    funext k; fin_cases k <;> simp
  have restoredQ := copy_move_exact (3 : Fin 4) 2 0 (by decide) (by decide)
    (machine suffix).computer.step (5 : Fin 11) 6 (executesAt_tm2 _ _ _ rfl)
    () (tapes [] (p ++ [false]) [] []) q.reverse [] suffix
  have restoreQ : RunsExactly (machine suffix).computer.step
      (cfg (5 : Fin 11) () (tapes suffix (p ++ [false]) [] q.reverse))
      (cfg (6 : Fin 11) () (tapes (q ++ suffix) (p ++ [false]) [] [])) (q.length + 1) := by
    convert restoredQ using 1 <;> try { unfold cfg; congr 1; funext k; fin_cases k }
    all_goals simp [cfg, tapes3, tapes]
    all_goals funext k; fin_cases k <;> rfl
  have movedP := copy_move_exact (1 : Fin 4) 3 2 (by decide) (by decide)
    (machine suffix).computer.step (6 : Fin 11) 7 (executesAt_tm2 _ _ _ rfl)
    () (tapes (q ++ suffix) [] [] []) (p ++ [false]) [] []
  have reverseP : RunsExactly (machine suffix).computer.step
      (cfg (6 : Fin 11) () (tapes (q ++ suffix) (p ++ [false]) [] []))
      (cfg (7 : Fin 11) () (tapes (q ++ suffix) [] (false :: p.reverse) [])) (p.length + 2) := by
    convert movedP using 1 <;> try { unfold cfg; congr 1; funext k; fin_cases k }
    all_goals simp [cfg, tapes3, tapes]
    all_goals funext k; fin_cases k <;> rfl
  have removeP : (machine suffix).computer.step
      (cfg (7 : Fin 11) () (tapes (q ++ suffix) [] (false :: p.reverse) [])) =
      some (cfg (8 : Fin 11) () (tapes (q ++ suffix) [] p.reverse [])) := by
    simp [machine, FinTM2.step, TM2.step, terminator, TM2.stepAux, cfg, tapes]
    funext k; fin_cases k <;> rfl
  have restoredP := copy_move_exact (2 : Fin 4) 1 0 (by decide) (by decide)
    (machine suffix).computer.step (8 : Fin 11) 9 (executesAt_tm2 _ _ _ rfl)
    () (tapes [] [] [] []) p.reverse [] (q ++ suffix)
  have restoreP : RunsExactly (machine suffix).computer.step
      (cfg (8 : Fin 11) () (tapes (q ++ suffix) [] p.reverse []))
      (cfg (9 : Fin 11) () (tapes (p ++ q ++ suffix) [] [] [])) (p.length + 1) := by
    convert restoredP using 1 <;> try { unfold cfg; congr 1; funext k; fin_cases k }
    all_goals simp [cfg, tapes3, tapes, List.append_assoc]
    all_goals funext k; fin_cases k <;> rfl
  have stopped : (machine suffix).computer.step
      (cfg (9 : Fin 11) () (tapes (p ++ q ++ suffix) [] [] [])) =
      some (haltList (machine suffix).computer (p ++ q ++ suffix)) := by
    rw [BinaryCompose.Machine.halt_eq]
    change some (⟨none, (none, ()), tapes (p ++ q ++ suffix) [] [] []⟩ : Cfg (Fin 4) (Fin 11) Unit) = _
    congr 2
    funext k; fin_cases k <;> rfl
  have all := (((((((first.trans reverseQ).trans (runsExactly_one removeQ)).trans (runsExactly_one load)).trans
    restoreQ).trans reverseP).trans (runsExactly_one removeP)).trans restoreP).trans (runsExactly_one stopped)
  rw [BinaryCompose.Machine.init_eq]
  have hi : BinaryCompose.wordTape (0 : Fin 4) (Holant.Algebraic.frame (p ++ [false]) ++ (q ++ [false])) =
      tapes (Holant.Algebraic.frame (p ++ [false]) ++ (q ++ [false])) [] [] [] := by
    funext k; fin_cases k <;> rfl
  change RunsExactly _ (cfg (0 : Fin 11) () _) _ _
  rw [hi]
  convert all using 1
  omega

end Holant.OneHot.StackProgram.GraphCodeMachine.Join
