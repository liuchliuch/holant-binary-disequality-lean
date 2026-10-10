import Holant.OneHot.StackProgram.Machine.Dynamic

/-! Exact framed opcode dispatch inside the persistent interpreter, preserving
its data stack and all cleaned worker tapes. -/
namespace Holant.OneHot.StackProgram.Machine.Dynamic
open Turing Computability Holant.Complexity BinaryCompose StackProtocol Family
variable {A : Type} [Fintype A] [DecidableEq A]
variable (workers : Op A → BinaryCompose.Machine) (labels : Encoding A Bool) (C : ℕ)

set_option backward.isDefEq.respectTransparency false

theorem fetch_cons (word code data : List Bool) :
    (machine workers labels C).computer.step
      (cfg (.inl 1) (initial workers) (tapes workers (true :: Holant.Algebraic.frame word ++ code) data [] [])) =
    some (cfg (.inl 2) (initial workers) (tapes workers (Holant.Algebraic.frame word ++ code) data [] [])) := by
  simp [machine, FinTM2.step, TM2.step, program, Dispatch.fetchStmt, cfg, TM2.stepAux, tapes]
  funext key
  cases key with
  | inl k => fin_cases k <;> rfl
  | inr pair => rfl

theorem fetch_exact (hlabels : ∀ a, (labels.encode a).length ≤ C)
    (op : Op A) (code data : List Bool) :
    RunsExactly (machine workers labels C).computer.step
      (cfg (.inl 1) (initial workers)
        (tapes workers (true :: Holant.Algebraic.frame (opEncode labels op) ++ code) data [] []))
      (cfg (control workers op 0) (initial workers) (tapes workers code data [] []))
      (2 * (opEncode labels op).length + 4) := by
  have first := runsExactly_one (fetch_cons workers labels C (opEncode labels op) code data)
  have hframe := GraphPreprocessing.Frame.extract_exact (.inl 0 : Keys workers) (.inl 2) (.inl 3)
    (by simp) (by simp) (by simp) (machine workers labels C).computer.step
    (.inl 2) (.inl 3) (.inl 4) (.inl 6)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    (initial workers) (tapes workers [] data [] []) (opEncode labels op) code []
  have second : RunsExactly (machine workers labels C).computer.step
      (cfg (.inl 2) (initial workers)
        (tapes workers (Holant.Algebraic.frame (opEncode labels op) ++ code) data [] []))
      (cfg (.inl 4) (initial workers) (tapes workers code data (opEncode labels op) []))
      (2 * ((opEncode labels op).length + 1)) := by
    convert hframe using 1 <;> congr 1 <;> funext key <;> cases key with
    | inl k => fin_cases k <;> simp [tapes3, tapes]
    | inr pair => simp [tapes3, tapes]
  have last : (machine workers labels C).computer.step
      (cfg (.inl 4) (initial workers) (tapes workers code data (opEncode labels op) [])) =
      some (cfg (control workers op 0) (initial workers) (tapes workers code data [] [])) := by
    have h := Dispatch.opcodeStmt_exact (.inl 2 : Keys workers)
      (fun op => control workers op 0) (.inl 6) labels (C + 6) op
      (opEncode_length_le labels C hlabels op) (initial workers) (tapes workers code data [] [])
    have hu : Function.update (tapes workers code data [] []) (.inl 2) (opEncode labels op) =
        tapes workers code data (opEncode labels op) [] := by
      funext key; cases key with
      | inl k => fin_cases k <;> rfl
      | inr pair => rfl
    have hz : Function.update (tapes workers code data [] []) (.inl 2) [] = tapes workers code data [] [] := by
      funext key; cases key with
      | inl k => fin_cases k <;> rfl
      | inr pair => rfl
    rw [hu, hz] at h
    exact congrArg some h
  convert (first.trans second).trans (runsExactly_one last) using 1
  omega

/-- One actual dispatch, clean worker execution, and return to the fetch loop. -/
theorem instruction_exact (hlabels : ∀ a, (labels.encode a).length ≤ C)
    (op : Op A) (code input output : List Bool) (time : ℕ)
    (hworker : Kernels.Executes (workers op) input output time) (hout : output ≠ []) :
    RunsExactly (machine workers labels C).computer.step
      (cfg (.inl 1) (initial workers)
        (tapes workers (true :: Holant.Algebraic.frame (opEncode labels op) ++ code) input [] []))
      (cfg (.inl 1) (initial workers) (tapes workers code output [] []))
      (time + 2 * (opEncode labels op).length + 2 * input.length + 2 * output.length + 9) := by
  have a := fetch_exact workers labels C hlabels op code input
  have b := a.trans (load_input workers labels C op code input)
  have c := b.trans (worker_run workers labels C op code input output time hworker)
  cases output with
  | nil => exact False.elim (hout rfl)
  | cons bit output =>
    have d := c.trans (runsExactly_one (check_output workers labels C op code bit output))
    have e := d.trans (return_output workers labels C op code (bit :: output))
    convert e using 1
    simp only [List.length_cons]
    omega

/-- The list terminator and its EOF check are consumed; no code is left at success. -/
theorem fetch_done (data : List Bool) :
    (machine workers labels C).computer.step
      (cfg (.inl 1) (initial workers) (tapes workers [false] data [] [])) =
    some (cfg (.inl 5) (initial workers) (tapes workers [] data [] [])) := by
  simp [machine, FinTM2.step, TM2.step, program, Dispatch.fetchStmt, cfg, TM2.stepAux, tapes]
  funext key
  cases key with
  | inl k => fin_cases k <;> rfl
  | inr pair => rfl

theorem start_exact (code : List Bool) :
    (machine workers labels C).computer.step
      (initList (machine workers labels C).computer code) =
    some (cfg (.inl 1) (initial workers) (tapes workers code [false] [] [])) := by
  rw [BinaryCompose.Machine.init_eq]
  simp [machine, FinTM2.step, TM2.step, program, cfg, TM2.stepAux]
  funext key
  cases key with
  | inl k => fin_cases k <;> simp [tapes, wordTape]
  | inr pair => simp [tapes, wordTape]

theorem finish (data : List Bool) :
    RunsExactly (machine workers labels C).computer.step
      (cfg (.inl 1) (initial workers) (tapes workers [false] data [] []))
      (haltList (machine workers labels C).computer data) 2 := by
  have last : (machine workers labels C).computer.step
      (cfg (.inl 5) (initial workers) (tapes workers [] data [] [])) =
      some (haltList (machine workers labels C).computer data) := by
    rw [BinaryCompose.Machine.halt_eq]
    change some (⟨none, (none, initial workers), tapes workers [] data [] []⟩ : Config workers) = _
    congr 2
    funext key
    cases key with
    | inl k => fin_cases k <;> simp [tapes, wordTape]
    | inr pair => simp [tapes, wordTape]
  exact (runsExactly_one (fetch_done workers labels C data)).trans (runsExactly_one last)

end Holant.OneHot.StackProgram.Machine.Dynamic
