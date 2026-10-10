import Holant.Complexity.StepCost

/-!
# Returning clear and copy protocols on actual binary stacks

Each routine is a finite TM2 statement with caller-supplied loop and return
labels. The only scratch memory is `Option Bool`; arbitrary caller memory and
unselected stacks are preserved. Local equations at the routine's labels suffice
to run the routine inside any larger ordinary or oracle transition system.

The execution theorems give exact numbers of actual transitions, followed by
mathlib timed contracts. No function on an unbounded configuration is added to a
program: all stack manipulation is performed by the displayed TM2 syntax.
-/

namespace Holant.Complexity.StackProtocol

open Turing
open Turing.TM2.Stmt

variable {K Λ τ : Type} [DecidableEq K]

abbrev Cfg (K Λ τ : Type) := TM2.Cfg (fun _ : K => Bool) Λ (Option Bool × τ)
abbrev Stmt (K Λ τ : Type) := TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × τ)

/-- Active control with the scratch register reset; caller memory is retained. -/
def cfg (label : Λ) (memory : τ) (tapes : K → List Bool) : Cfg K Λ τ :=
  ⟨some label, (none, memory), tapes⟩

/-- The surrounding machine executes the given concrete statement at this label. -/
def ExecutesAt (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (label : Λ)
    (stmt : Stmt K Λ τ) : Prop :=
  ∀ state tapes, step ⟨some label, state, tapes⟩ = some (TM2.stepAux stmt state tapes)

/-- A local ordinary-program equation discharges the operational interface. -/
theorem executesAt_tm2 (program : Λ → Stmt K Λ τ) (label : Λ) (stmt : Stmt K Λ τ)
    (h : program label = stmt) : ExecutesAt (TM2.step program) label stmt := by
  intro state tapes
  simp [TM2.step, h]

/-- Discard one symbol per transition, or return when the selected stack is empty. -/
def clearStmt (stack : K) (loop next : Λ) : Stmt K Λ τ :=
  pop stack (fun v bit => (bit, v.2)) (branch (fun v => v.1.isSome)
    (load (fun v => (none, v.2)) (goto (fun _ => loop)))
    (load (fun v => (none, v.2)) (goto (fun _ => next))))

/-- Move and reverse the source onto temporary storage, one symbol per transition. -/
def copyMoveStmt (src tmp : K) (loop next : Λ) : Stmt K Λ τ :=
  pop src (fun v bit => (bit, v.2)) (branch (fun v => v.1.isSome)
    (push tmp (fun v => v.1.getD false)
      (load (fun v => (none, v.2)) (goto (fun _ => loop))))
    (load (fun v => (none, v.2)) (goto (fun _ => next))))

/-- Restore the source and prepend its ordered copy onto destination. -/
def copyRestoreStmt (src dst tmp : K) (loop next : Λ) : Stmt K Λ τ :=
  pop tmp (fun v bit => (bit, v.2)) (branch (fun v => v.1.isSome)
    (push src (fun v => v.1.getD false) (push dst (fun v => v.1.getD false)
      (load (fun v => (none, v.2)) (goto (fun _ => loop)))))
    (load (fun v => (none, v.2)) (goto (fun _ => next))))

omit [DecidableEq K] in
@[simp] theorem clearStmt_budget (stack : K) (loop next : Λ) :
    TM2Cost.budget (clearStmt (τ := τ) stack loop next) = 4 := rfl

omit [DecidableEq K] in
@[simp] theorem copyMoveStmt_budget (src tmp : K) (loop next : Λ) :
    TM2Cost.budget (copyMoveStmt (τ := τ) src tmp loop next) = 5 := rfl

omit [DecidableEq K] in
@[simp] theorem copyRestoreStmt_budget (src dst tmp : K) (loop next : Λ) :
    TM2Cost.budget (copyRestoreStmt (τ := τ) src dst tmp loop next) = 6 := rfl

/-- Exact iteration, retaining a resulting active or halted configuration. -/
def RunsExactly (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (a b : Cfg K Λ τ)
    (time : ℕ) : Prop :=
  (fun c => c.bind step)^[time] (some a) = some b

omit [DecidableEq K] in
theorem runsExactly_one {step : Cfg K Λ τ → Option (Cfg K Λ τ)}
    {a b : Cfg K Λ τ} (h : step a = some b) : RunsExactly step a b 1 := h

omit [DecidableEq K] in
theorem RunsExactly.trans {step : Cfg K Λ τ → Option (Cfg K Λ τ)}
    {a b c : Cfg K Λ τ} {n m : ℕ}
    (h : RunsExactly step a b n) (h' : RunsExactly step b c m) :
    RunsExactly step a c (m + n) := by
  unfold RunsExactly at *
  rw [Function.iterate_add_apply, h, h']

/-- Exact executions furnish timed witnesses with precisely the displayed count. -/
def RunsExactly.toTimed {step : Cfg K Λ τ → Option (Cfg K Λ τ)}
    {a b : Cfg K Λ τ} {n : ℕ} (h : RunsExactly step a b n) :
    StateTransition.EvalsToInTime step a (some b) n where
  steps := n
  evals_in_steps := h
  steps_le_m := Nat.le_refl n

theorem clear_step_cons (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (stack : K) (loop next : Λ) (h : ExecutesAt step loop (clearStmt stack loop next))
    (memory : τ) (tapes : K → List Bool) (bit : Bool) (word : List Bool) :
    step (cfg loop memory (Function.update tapes stack (bit :: word))) =
      some (cfg loop memory (Function.update tapes stack word)) := by
  rw [cfg, h]
  simp [clearStmt, TM2.stepAux, cfg, Function.update_idem]

theorem clear_step_nil (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (stack : K) (loop next : Λ) (h : ExecutesAt step loop (clearStmt stack loop next))
    (memory : τ) (tapes : K → List Bool) :
    step (cfg loop memory (Function.update tapes stack [])) =
      some (cfg next memory (Function.update tapes stack [])) := by
  rw [cfg, h]
  simp [clearStmt, TM2.stepAux, cfg, Function.update_idem]

theorem clear_exact_update (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (stack : K) (loop next : Λ) (h : ExecutesAt step loop (clearStmt stack loop next))
    (memory : τ) (tapes : K → List Bool) (word : List Bool) :
    RunsExactly step (cfg loop memory (Function.update tapes stack word))
      (cfg next memory (Function.update tapes stack [])) (word.length + 1) := by
  induction word with
  | nil => exact runsExactly_one (clear_step_nil step stack loop next h memory tapes)
  | cons bit word ih =>
    exact (runsExactly_one (clear_step_cons step stack loop next h memory tapes bit word)).trans ih

/-- Clear exactly one stack in its original length plus one transitions. -/
theorem clear_exact (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (stack : K) (loop next : Λ) (h : ExecutesAt step loop (clearStmt stack loop next))
    (memory : τ) (tapes : K → List Bool) :
    RunsExactly step (cfg loop memory tapes)
      (cfg next memory (Function.update tapes stack [])) ((tapes stack).length + 1) := by
  simpa using clear_exact_update step stack loop next h memory tapes (tapes stack)

/-- Timed clear contract, preserving every other stack and all caller memory. -/
def clear_correct (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (stack : K) (loop next : Λ) (h : ExecutesAt step loop (clearStmt stack loop next))
    (memory : τ) (tapes : K → List Bool) :
    StateTransition.EvalsToInTime step (cfg loop memory tapes)
      (some (cfg next memory (Function.update tapes stack []))) ((tapes stack).length + 1) :=
  (clear_exact step stack loop next h memory tapes).toTimed

/-- A frame with three selected stacks replaced; all other stacks stay unchanged. -/
def tapes3 (frame : K → List Bool) (src dst tmp : K)
    (source destination temporary : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update frame src source) dst destination) tmp temporary

section Copy

variable (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)

include hsd hst in
@[simp] theorem tapes3_src (frame : K → List Bool) (source destination temporary : List Bool) :
    tapes3 frame src dst tmp source destination temporary src = source := by
  simp [tapes3, hsd, hst]

include hdt in
@[simp] theorem tapes3_dst (frame : K → List Bool) (source destination temporary : List Bool) :
    tapes3 frame src dst tmp source destination temporary dst = destination := by
  simp [tapes3, hdt]

@[simp] theorem tapes3_tmp (frame : K → List Bool) (source destination temporary : List Bool) :
    tapes3 frame src dst tmp source destination temporary tmp = temporary := by
  simp [tapes3]

theorem tapes3_other (frame : K → List Bool) (source destination temporary : List Bool)
    (k : K) (hs : k ≠ src) (hd : k ≠ dst) (ht : k ≠ tmp) :
    tapes3 frame src dst tmp source destination temporary k = frame k := by
  simp [tapes3, hs, hd, ht]

include hsd hst in
@[simp] theorem update_tapes3_src (frame : K → List Bool)
    (source destination temporary word : List Bool) :
    Function.update (tapes3 frame src dst tmp source destination temporary) src word =
      tapes3 frame src dst tmp word destination temporary := by
  funext k
  by_cases h : k = src
  · subst k; simp [tapes3, hsd, hst]
  · simp [tapes3, Function.update_apply, h]

include hdt in
@[simp] theorem update_tapes3_dst (frame : K → List Bool)
    (source destination temporary word : List Bool) :
    Function.update (tapes3 frame src dst tmp source destination temporary) dst word =
      tapes3 frame src dst tmp source word temporary := by
  funext k
  by_cases h : k = dst
  · subst k; simp [tapes3, hdt]
  · simp [tapes3, Function.update_apply, h]

@[simp] theorem update_tapes3_tmp (frame : K → List Bool)
    (source destination temporary word : List Bool) :
    Function.update (tapes3 frame src dst tmp source destination temporary) tmp word =
      tapes3 frame src dst tmp source destination word := by
  simp [tapes3, Function.update_idem]

include hsd hst in
theorem copy_move_step_cons (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (loop next : Λ) (h : ExecutesAt step loop (copyMoveStmt src tmp loop next))
    (memory : τ) (frame : K → List Bool) (bit : Bool)
    (source destination temporary : List Bool) :
    step (cfg loop memory (tapes3 frame src dst tmp (bit :: source) destination temporary)) =
      some (cfg loop memory (tapes3 frame src dst tmp source destination (bit :: temporary))) := by
  rw [cfg, h]
  simp [copyMoveStmt, TM2.stepAux, cfg, tapes3_src src dst tmp hsd hst,
    update_tapes3_src src dst tmp hsd hst]

include hsd hst in
theorem copy_move_step_nil (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (loop next : Λ) (h : ExecutesAt step loop (copyMoveStmt src tmp loop next))
    (memory : τ) (frame : K → List Bool) (destination temporary : List Bool) :
    step (cfg loop memory (tapes3 frame src dst tmp [] destination temporary)) =
      some (cfg next memory (tapes3 frame src dst tmp [] destination temporary)) := by
  rw [cfg, h]
  simp [copyMoveStmt, TM2.stepAux, cfg, tapes3_src src dst tmp hsd hst,
    update_tapes3_src src dst tmp hsd hst]

include hsd hst hdt in
theorem copy_restore_step_cons (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (loop next : Λ) (h : ExecutesAt step loop (copyRestoreStmt src dst tmp loop next))
    (memory : τ) (frame : K → List Bool) (bit : Bool)
    (source destination temporary : List Bool) :
    step (cfg loop memory (tapes3 frame src dst tmp source destination (bit :: temporary))) =
      some (cfg loop memory
        (tapes3 frame src dst tmp (bit :: source) (bit :: destination) temporary)) := by
  rw [cfg, h]
  simp [copyRestoreStmt, TM2.stepAux, cfg, tapes3_src src dst tmp hsd hst,
    tapes3_dst src dst tmp hdt, update_tapes3_src src dst tmp hsd hst,
    update_tapes3_dst src dst tmp hdt]

theorem copy_restore_step_nil (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (loop next : Λ) (h : ExecutesAt step loop (copyRestoreStmt src dst tmp loop next))
    (memory : τ) (frame : K → List Bool) (source destination : List Bool) :
    step (cfg loop memory (tapes3 frame src dst tmp source destination [])) =
      some (cfg next memory (tapes3 frame src dst tmp source destination [])) := by
  rw [cfg, h]
  simp [copyRestoreStmt, TM2.stepAux, cfg]

include hsd hst in
theorem copy_move_exact (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (loop next : Λ) (h : ExecutesAt step loop (copyMoveStmt src tmp loop next))
    (memory : τ) (frame : K → List Bool) (source destination temporary : List Bool) :
    RunsExactly step (cfg loop memory (tapes3 frame src dst tmp source destination temporary))
      (cfg next memory (tapes3 frame src dst tmp [] destination (source.reverse ++ temporary)))
      (source.length + 1) := by
  induction source generalizing temporary with
  | nil => exact runsExactly_one (copy_move_step_nil src dst tmp hsd hst step loop next h
      memory frame destination temporary)
  | cons bit source ih =>
    have run := (runsExactly_one (copy_move_step_cons src dst tmp hsd hst step loop next h
      memory frame bit source destination temporary)).trans (ih (bit :: temporary))
    simpa [List.reverse_cons, List.append_assoc] using run

include hsd hst hdt in
theorem copy_restore_exact (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (loop next : Λ) (h : ExecutesAt step loop (copyRestoreStmt src dst tmp loop next))
    (memory : τ) (frame : K → List Bool) (temporary source destination : List Bool) :
    RunsExactly step (cfg loop memory (tapes3 frame src dst tmp source destination temporary))
      (cfg next memory (tapes3 frame src dst tmp (temporary.reverse ++ source)
        (temporary.reverse ++ destination) [])) (temporary.length + 1) := by
  induction temporary generalizing source destination with
  | nil => exact runsExactly_one (copy_restore_step_nil src dst tmp step loop next h
      memory frame source destination)
  | cons bit temporary ih =>
    have run := (runsExactly_one (copy_restore_step_cons src dst tmp hsd hst hdt step loop next h
      memory frame bit source destination temporary)).trans (ih (bit :: source) (bit :: destination))
    simpa [List.reverse_cons, List.append_assoc] using run

include hsd hst hdt in
/-- Exact copy on an explicit frame, with initially and finally empty temporary. -/
theorem copy_exact_frame (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (move restore next : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyRestoreStmt src dst tmp restore next))
    (memory : τ) (frame : K → List Bool) (source destination : List Bool) :
    RunsExactly step (cfg move memory (tapes3 frame src dst tmp source destination []))
      (cfg next memory (tapes3 frame src dst tmp source (source ++ destination) []))
      (2 * (source.length + 1)) := by
  have moveRun := copy_move_exact src dst tmp hsd hst step move restore hm
    memory frame source destination []
  simp only [List.append_nil] at moveRun
  have run := moveRun.trans
    (copy_restore_exact src dst tmp hsd hst hdt step restore next hr
      memory frame source.reverse [] destination)
  simpa [Nat.two_mul] using run

include hsd hst hdt in
/-- Copy preserves source, scratch emptiness, all unrelated stacks and caller memory;
only destination gains the source prefix. The return label remains active. -/
theorem copy_exact (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (move restore next : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyRestoreStmt src dst tmp restore next))
    (memory : τ) (tapes : K → List Bool) (htmp : tapes tmp = []) :
    RunsExactly step (cfg move memory tapes)
      (cfg next memory (Function.update tapes dst (tapes src ++ tapes dst)))
      (2 * ((tapes src).length + 1)) := by
  have hbefore : tapes3 tapes src dst tmp (tapes src) (tapes dst) [] = tapes := by
    simp [tapes3, ← htmp]
  have hafter : tapes3 tapes src dst tmp (tapes src) (tapes src ++ tapes dst) [] =
      Function.update tapes dst (tapes src ++ tapes dst) := by
    funext k
    by_cases ht : k = tmp
    · subst k; simp [tapes3, Ne.symm hdt, htmp]
    · simp [tapes3, Function.update_apply, ht]
  simpa only [hbefore, hafter] using copy_exact_frame src dst tmp hsd hst hdt step
    move restore next hm hr memory tapes (tapes src) (tapes dst)

/-- A linear timed contract for use inside finite ordinary or oracle machines. -/
def copy_correct (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (move restore next : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyRestoreStmt src dst tmp restore next))
    (memory : τ) (tapes : K → List Bool) (htmp : tapes tmp = []) :
    StateTransition.EvalsToInTime step (cfg move memory tapes)
      (some (cfg next memory (Function.update tapes dst (tapes src ++ tapes dst))))
      (2 * ((tapes src).length + 1)) :=
  (copy_exact src dst tmp hsd hst hdt step move restore next hm hr memory tapes htmp).toTimed

end Copy
end Holant.Complexity.StackProtocol
