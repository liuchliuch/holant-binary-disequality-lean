import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Syntax
import Holant.OneHot.StackProgram.Machine.Kernels

namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components
open Turing Computability Holant.Complexity BinaryCompose StackProtocol
variable (m : BinaryCompose.Machine) (z o a p : List Bool)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev startPhase (i : Fin 3) : Fin 26 := ⟨4 + 4 * i.val, by omega⟩
abbrev restorePhase (i : Fin 3) : Fin 26 := ⟨5 + 4 * i.val, by omega⟩
abbrev stripPhase (i : Fin 3) : Fin 26 := ⟨7 + 4 * i.val, by omega⟩
def afterPhase (i : Fin 3) : Fin 26 := if i = 0 then 20 else if i = 1 then 12 else 16

def base (input descriptor output count : List Bool) : Keys m → List Bool :=
  tapes m input descriptor [] output [] count

def active (phase : Fin 26) (input descriptor output count : List Bool) : Config m :=
  cfg (.inr phase) m.initial (base m input descriptor output count)

theorem embed_frame (i : Fin 3) (frame other : Fin 6 → List Bool)
    (q : TM2.Stmt (fun _ : m.K => Bool) m.Label m.State) :
    embedStmt (layout m frame) (states m) (fun l => (Sum.inl (i, l) : Labels m))
      (some (.inr (returnPhase i))) q =
    embedStmt (layout m other) (states m) (fun l => (Sum.inl (i, l) : Labels m))
      (some (.inr (returnPhase i))) q := by
  induction q <;> simp only [embedStmt, *] <;> rfl

/-- The closed compiler returns without changing any caller tape or time count. -/
theorem worker_exact (i : Fin 3) (input descriptor output count word result : List Bool)
    (time : ℕ) (h : Machine.Kernels.Executes m word result time) :
    RunsExactly (machine m z o a p).computer.step
      (cfg (.inl (i, m.main)) m.initial
        (Function.update (base m input descriptor output count) (.inl m.input) word))
      (cfg (.inr (returnPhase i)) m.initial
        (Function.update (base m input descriptor output count) (.inl m.output) result)) time := by
  have hr := embed_run (layout m ![input, descriptor, [], output, [], count]) (states m)
    (fun l => (Sum.inl (i, l) : Labels m)) (some (.inr (returnPhase i))) m.program (program m z o a p)
    (fun l => embed_frame m i (fun _ => []) _ (m.program l))
    (initList m.computer word) (haltList m.computer result) time h
  rw [BinaryCompose.Machine.init_eq, BinaryCompose.Machine.halt_eq] at hr
  simpa only [embedCfg, Option.elim_some, Option.elim_none, states, layout,
    wordTape, MachineFrame.update_left, base, tapes, cfg, RunsExactly, machine, FinTM2.step] using hr

/-- A frame moves directly into the real compiler input, charging both scans. -/
theorem load_exact (i : Fin 3) (input descriptor output count word : List Bool) :
    RunsExactly (machine m z o a p).computer.step
      (active m (startPhase i) input (Holant.Algebraic.frame word ++ descriptor) output count)
      (cfg (.inl (i, m.main)) m.initial
        (Function.update (base m input descriptor output count) (.inl m.input) word))
      (2 * (word.length + 1)) := by
  have hs : (machine m z o a p).program (.inr (startPhase i)) =
      GraphPreprocessing.Frame.scanStmt (.inr 1) (.inr 2) (.inr (startPhase i))
        (.inr (restorePhase i)) (.inr 25) := by fin_cases i <;> rfl
  have hr : (machine m z o a p).program (.inr (restorePhase i)) =
      copyMoveStmt (.inr 2) (.inl m.input) (.inr (restorePhase i)) (.inl (i, m.main)) := by
    fin_cases i <;> rfl
  have h := GraphPreprocessing.Frame.extract_exact (.inr 1 : Keys m) (.inl m.input) (.inr 2)
    (by simp) (by simp) (by simp) (machine m z o a p).computer.step
    (.inr (startPhase i)) (.inr (restorePhase i)) (.inl (i, m.main)) (.inr 25)
    (executesAt_tm2 _ _ _ hs) (executesAt_tm2 _ _ _ hr)
    m.initial (base m input descriptor output count) word descriptor []
  have hstart : tapes3 (base m input descriptor output count) (.inr 1) (.inl m.input) (.inr 2)
      (Holant.Algebraic.frame word ++ descriptor) [] [] =
      base m input (Holant.Algebraic.frame word ++ descriptor) output count := by
    funext key; cases key with
    | inl k => simp [base, tapes, tapes3, Function.update]
    | inr k => fin_cases k <;> simp [base, tapes, tapes3, Function.update]
  have hend : tapes3 (base m input descriptor output count) (.inr 1) (.inl m.input) (.inr 2)
      descriptor (word ++ []) [] = Function.update (base m input descriptor output count) (.inl m.input) word := by
    funext key; cases key with
    | inl k => simp [base, tapes, tapes3, Function.update]
    | inr k => fin_cases k <;> simp [base, tapes, tapes3, Function.update]
  rw [hstart, hend] at h
  exact h

/-- A compiler result is reversed into the persistent output and its sole list
terminator is checked and removed. Every worker tape finishes empty. -/
theorem return_exact (i : Fin 3) (input descriptor output count word : List Bool) :
    RunsExactly (machine m z o a p).computer.step
      (cfg (.inr (returnPhase i)) m.initial
        (Function.update (base m input descriptor output count) (.inl m.output) (word ++ [false])))
      (active m (afterPhase i) input descriptor (word.reverse ++ output) count)
      (word.length + 3) := by
  have hp : (machine m z o a p).program (.inr (returnPhase i)) =
      copyMoveStmt (.inl m.output) (.inr 3) (.inr (returnPhase i)) (.inr (stripPhase i)) := by
    fin_cases i <;> rfl
  have h := copy_move_exact (.inl m.output : Keys m) (.inr 5) (.inr 3)
    (by simp) (by simp) (machine m z o a p).computer.step
    (.inr (returnPhase i)) (.inr (stripPhase i)) (executesAt_tm2 _ _ _ hp)
    m.initial (base m input descriptor output count) (word ++ [false]) count output
  have moved : RunsExactly (machine m z o a p).computer.step
      (cfg (.inr (returnPhase i)) m.initial
        (Function.update (base m input descriptor output count) (.inl m.output) (word ++ [false])))
      (active m (stripPhase i) input descriptor (false :: word.reverse ++ output) count)
      (word.length + 2) := by
    have hstart : tapes3 (base m input descriptor output count) (.inl m.output) (.inr 5) (.inr 3)
        (word ++ [false]) count output =
        Function.update (base m input descriptor output count) (.inl m.output) (word ++ [false]) := by
      funext key; cases key with
      | inl k => simp [base, tapes, tapes3, Function.update]
      | inr k => fin_cases k <;> simp [base, tapes, tapes3, Function.update]
    have hend : tapes3 (base m input descriptor output count) (.inl m.output) (.inr 5) (.inr 3)
        [] count ((word ++ [false]).reverse ++ output) =
        base m input descriptor (false :: word.reverse ++ output) count := by
      funext key; cases key with
      | inl k => simp [base, tapes, tapes3, Function.update]
      | inr k => fin_cases k <;> simp [base, tapes, tapes3, Function.update]
    rw [hstart, hend] at h
    simpa [active, Nat.add_assoc] using h
  have stripped : (machine m z o a p).computer.step
      (active m (stripPhase i) input descriptor (false :: word.reverse ++ output) count) =
      some (active m (afterPhase i) input descriptor (word.reverse ++ output) count) := by
    have hp : (machine m z o a p).program (.inr (stripPhase i)) = stripStmt m (afterPhase i) := by
      fin_cases i <;> rfl
    change some (TM2.stepAux ((machine m z o a p).program (.inr (stripPhase i)))
      (none, m.initial) (base m input descriptor (false :: word.reverse ++ output) count)) = _
    rw [hp]
    change some (cfg (Sum.inr (afterPhase i) : Labels m) m.initial
      (Function.update (base m input descriptor (false :: word.reverse ++ output) count)
        (.inr 3) (word.reverse ++ output))) = _
    congr 2
    funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using moved.trans (runsExactly_one stripped)

/-- Full real subroutine call with the framing, compiler and cleanup costs exposed. -/
theorem call_exact (i : Fin 3) (input descriptor output count word result : List Bool)
    (time : ℕ) (h : Machine.Kernels.Executes m word (result ++ [false]) time) :
    RunsExactly (machine m z o a p).computer.step
      (active m (startPhase i) input (Holant.Algebraic.frame word ++ descriptor) output count)
      (active m (afterPhase i) input descriptor (result.reverse ++ output) count)
      (2 * word.length + time + result.length + 5) := by
  have all := ((load_exact m z o a p i input descriptor output count word).trans
    (worker_exact m z o a p i input descriptor output count word (result ++ [false]) time h)).trans
    (return_exact m z o a p i input descriptor output count result)
  convert all using 1
  omega

end Holant.OneHot.StackProgram.GraphCodeMachine.Components
