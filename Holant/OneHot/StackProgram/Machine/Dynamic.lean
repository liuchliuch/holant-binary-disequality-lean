import Holant.OneHot.StackProgram.Machine.Family

/-! One fixed finite Boolean-stack interpreter reads arbitrarily long bytecode.
Its finite opcode family is embedded once. Code and value stacks are transferred
by real bit loops, and each dispatched worker returns to the same fetch loop. -/
namespace Holant.OneHot.StackProgram.Machine.Dynamic
open Turing Computability Holant.Complexity BinaryCompose StackProtocol
open Family Turing.TM2.Stmt
variable {A : Type} [Fintype A] [DecidableEq A]
variable (workers : Op A → BinaryCompose.Machine) (labels : Encoding A Bool) (C : ℕ)

set_option backward.isDefEq.respectTransparency false

/-- A worker must return a nonempty encoded stack. Empty output signals failure. -/
def checkStmt (op : Op A) : Statement workers :=
  peek (workerKey workers op (workers op).output) (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (load (fun v => (none, v.2)) (goto (fun _ => control workers op 3)))
      (load (fun v => (none, v.2)) (goto (fun _ => .inl 6))))

/-- The interpreter uses only finite control and Boolean push/pop/peek operations.
Label six is an explicit rejecting halt, potentially retaining diagnostic tapes. -/
def program : Labels workers → Statement workers
  | .inl i =>
    if i = 0 then push (.inl 1) (fun _ => false) (goto (fun _ => .inl 1))
    else if i = 1 then Dispatch.fetchStmt (.inl 0) (.inl 2) (.inl 5) (.inl 6)
    else if i = 2 then GraphPreprocessing.Frame.scanStmt (.inl 0) (.inl 3)
      (.inl 2) (.inl 3) (.inl 6)
    else if i = 3 then copyMoveStmt (.inl 3) (.inl 2) (.inl 3) (.inl 4)
    else if i = 4 then Dispatch.opcodeStmt (.inl 2) (fun op => control workers op 0)
      (.inl 6) labels (C + 6)
    else .halt
  | .inr ⟨op, .inl i⟩ =>
    if i = 0 then copyMoveStmt (.inl 1) (.inl 3) (control workers op 0) (control workers op 1)
    else if i = 1 then copyMoveStmt (.inl 3) (workerKey workers op (workers op).input)
      (control workers op 1) (workerLabel workers op (workers op).main)
    else if i = 2 then checkStmt workers op
    else if i = 3 then copyMoveStmt (workerKey workers op (workers op).output) (.inl 3)
      (control workers op 3) (control workers op 4)
    else copyMoveStmt (.inl 3) (.inl 1) (control workers op 4) (.inl 1)
  | .inr ⟨op, .inr label⟩ =>
    embedStmt (layout workers op (fun _ => [])) (states workers op)
      (workerLabel workers op) (some (control workers op 2)) ((workers op).program label)

abbrev machine : BinaryCompose.Machine where
  K := Keys workers
  input := .inl 0
  output := .inl 1
  Label := Labels workers
  main := .inl 0
  State := States workers
  initial := (none, initial workers)
  program := program workers labels C

/-- Every successful worker execution preserves the complete remaining bytecode. -/
theorem worker_run (op : Op A) (code input output : List Bool) (time : ℕ)
    (h : Kernels.Executes (workers op) input output time) :
    RunsExactly (machine workers labels C).computer.step
      (cfg (workerLabel workers op (workers op).main) (initial workers)
        (Function.update (tapes workers code [] [] []) (workerKey workers op (workers op).input) input))
      (cfg (control workers op 2) (initial workers)
        (Function.update (tapes workers code [] [] []) (workerKey workers op (workers op).output) output)) time := by
  have hr := embed_run (layout workers op ![code, [], [], []]) (states workers op)
    (workerLabel workers op) (some (control workers op 2)) (workers op).program
    (program workers labels C)
    (fun label => embed_frame workers op (fun _ => []) ![code, [], [], []] ((workers op).program label))
    (initList (workers op).computer input) (haltList (workers op).computer output) time h
  rw [BinaryCompose.Machine.init_eq, BinaryCompose.Machine.halt_eq] at hr
  simp only [embedCfg, Option.elim_some, Option.elim_none, states_initial, layout_word] at hr
  have htapes : Sum.elim ![code, [], [], []] (fun _ => []) = tapes workers code [] [] [] := by
    funext k; cases k <;> rfl
  rw [htapes] at hr
  exact hr

/-- Input transfer reverses twice, charges both EOF tests, and cleans scratch. -/
theorem load_input (op : Op A) (code input : List Bool) :
    RunsExactly (machine workers labels C).computer.step
      (cfg (control workers op 0) (initial workers) (tapes workers code input [] []))
      (cfg (workerLabel workers op (workers op).main) (initial workers)
        (Function.update (tapes workers code [] [] []) (workerKey workers op (workers op).input) input))
      (2 * (input.length + 1)) := by
  have hr := StackWord.move_exact (.inl 1 : Keys workers)
    (workerKey workers op (workers op).input) (.inl 3)
    (by simp [workerKey]) (by simp) (by simp [workerKey])
    (machine workers labels C).computer.step (control workers op 0) (control workers op 1)
    (workerLabel workers op (workers op).main)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    (initial workers) (tapes workers code [] [] []) input []
  convert hr using 1 <;> congr 1 <;> funext key <;> cases key with
  | inl k => fin_cases k <;> simp [tapes3, tapes, workerKey, Function.update]
  | inr pair =>
    simp only [tapes3, Function.update_apply, Sum.inr_ne_inl, ↓reduceIte, tapes, List.append_nil, ite_self]

/-- A nonempty successful output passes the explicit failure check. -/
theorem check_output (op : Op A) (code : List Bool) (bit : Bool) (output : List Bool) :
    (machine workers labels C).computer.step
      (cfg (control workers op 2) (initial workers)
        (Function.update (tapes workers code [] [] []) (workerKey workers op (workers op).output) (bit :: output))) =
    some (cfg (control workers op 3) (initial workers)
        (Function.update (tapes workers code [] [] []) (workerKey workers op (workers op).output) (bit :: output))) := by
  simp [machine, FinTM2.step, TM2.step, program, Family.control, checkStmt, cfg, TM2.stepAux]

/-- The clean worker output is returned intact to the persistent data stack. -/
theorem return_output (op : Op A) (code output : List Bool) :
    RunsExactly (machine workers labels C).computer.step
      (cfg (control workers op 3) (initial workers)
        (Function.update (tapes workers code [] [] []) (workerKey workers op (workers op).output) output))
      (cfg (.inl 1) (initial workers) (tapes workers code output [] []))
      (2 * (output.length + 1)) := by
  have hr := StackWord.move_exact (workerKey workers op (workers op).output)
    (.inl 1 : Keys workers) (.inl 3)
    (by simp [workerKey]) (by simp [workerKey]) (by simp)
    (machine workers labels C).computer.step (control workers op 3) (control workers op 4) (.inl 1)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    (initial workers) (tapes workers code [] [] []) output []
  convert hr using 1 <;> congr 1 <;> funext key <;> cases key with
  | inl k => fin_cases k <;> simp [tapes3, tapes, workerKey, Function.update]
  | inr pair =>
    simp only [tapes3, Function.update_apply, Sum.inr_ne_inl, ↓reduceIte, tapes, ite_self]

end Holant.OneHot.StackProgram.Machine.Dynamic
