import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.Exactness.Rows

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

Ordered rows and all retained/new references of the existing primitive
machines. Fixed blank blocks are compared including suffix gate indices.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Exactness


open Turing BitLayout OutputMachine PrimitiveMachines
open scoped Classical

theorem emptyBlock_eq {I O : Type} [Fintype O] [DecidableEq O] (bits : O → Bool) (env : I → ℕ) :
    PrimitiveMachines.emptyBlock O bits = FiniteMachine.result
      (Rows.tabulate (fixedEnum O) mem_fixedEnum (fun o => Rows.constant (bits o)) env) :=
  congrArg FiniteMachine.result (constant_tabulate_independent bits (fixedEnum O) mem_fixedEnum
    (fun _ : Unit => 0) env)

variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]

theorem readState_eq (env : Address tm C → ℕ) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    PrimitiveMachines.readState tm k f (C, (addresses tm C).map env) =
      packedResult tm C (StatementRows.readState tm C k f env) := by
  rw [PrimitiveMachines.readState, attach, headRefs_pack, shift_map]
  have hr := Routing.state_eq tm C (Rows.shift (Emit.table₂Cost f) env)
    (Rows.table₂ f (fun a => env (PrimitiveBlocks.headRoute tm C k a))).2
  apply Prod.ext
  · simp [packedResult, FiniteMachine.result, StatementRows.readState, Rows.renameOutput,
      Rows.seq, Rows.parallel, Rows.route, Rows.renameInput, PrimitiveBlocks.stateRoute]
  · simpa [Routing.input, packedResult, FiniteMachine.result, StatementRows.readState,
      Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route, Rows.renameInput,
      table₂_length, shift_zero] using hr

theorem push_eq (env : Address tm C → ℕ) (k : tm.K) (f : tm.σ → tm.Γ k) :
    PrimitiveMachines.push tm k f (C, (addresses tm C).map env) =
      packedResult tm C (StatementRows.push tm C k f env) := by
  rw [PrimitiveMachines.push, attach, stateRefs_pack, shift_map]
  have hr := Routing.push_eq tm C k (Rows.shift (Emit.tableCost (fun s => some (f s))) env)
    (Rows.table (fun s => some (f s)) (fun s => env (stateAddr tm C s))).2
  apply Prod.ext
  · simp [packedResult, FiniteMachine.result, StatementRows.push, Rows.renameOutput,
      Rows.seq, Rows.parallel, Rows.route, Rows.renameInput, PrimitiveBlocks.stateRoute]
  · simpa [Routing.input, packedResult, FiniteMachine.result, StatementRows.push,
      Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route, Rows.renameInput,
      PrimitiveMachines.table_length, PrimitiveBlocks.stateRoute, shift_zero] using hr

theorem goto_eq (env : Address tm C → ℕ) (f : tm.σ → tm.Λ) :
    PrimitiveMachines.goto tm f (C, (addresses tm C).map env) =
      packedResult tm C (StatementRows.goto tm C f env) := by
  rw [PrimitiveMachines.goto, attach, stateRefs_pack, shift_map]
  have hr := Routing.label_eq tm C (Rows.shift (Emit.tableCost (fun s => some (f s))) env)
    (Rows.table (fun s => some (f s)) (fun s => env (stateAddr tm C s))).2
  apply Prod.ext
  · simp [packedResult, FiniteMachine.result, StatementRows.goto, Rows.renameOutput,
      Rows.seq, Rows.parallel, Rows.route, Rows.renameInput, PrimitiveBlocks.stateRoute]
  · simpa [Routing.input, packedResult, FiniteMachine.result, StatementRows.goto,
      Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route, Rows.renameInput,
      PrimitiveMachines.table_length, PrimitiveBlocks.stateRoute, shift_zero] using hr

theorem pop_eq (env : Address tm C → ℕ) (k : tm.K) :
    PrimitiveMachines.pop tm k (C, (addresses tm C).map env) =
      packedResult tm C (StatementRows.pop tm C k env) := by
  rw [PrimitiveMachines.pop, attach, emptyBlock_eq _ env, shift_map]
  have hr := Routing.pop_eq tm C k (Rows.shift (Fintype.card (Option (tm.Γ k))) env)
    (Rows.tabulate (fixedEnum (Option (tm.Γ k))) mem_fixedEnum
      (fun a => Rows.constant (oneHot (none : Option (tm.Γ k)) a)) env).2
  apply Prod.ext
  · simp [packedResult, FiniteMachine.result, StatementRows.pop, Rows.renameOutput,
      Rows.seq, Rows.parallel, Rows.route, shift_zero]
  · simpa [Routing.input, packedResult, FiniteMachine.result, StatementRows.pop,
      Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route,
      constant_tabulate_length, shift_zero] using hr

theorem halt_eq (env : Address tm C → ℕ) :
    PrimitiveMachines.halt tm (C, (addresses tm C).map env) =
      packedResult tm C (StatementRows.halt tm C env) := by
  rw [PrimitiveMachines.halt, attach, emptyBlock_eq _ env, shift_map]
  have hr := Routing.label_eq tm C (Rows.shift (Fintype.card (Option tm.Λ)) env)
    (Rows.tabulate (fixedEnum (Option tm.Λ)) mem_fixedEnum
      (fun l => Rows.constant (oneHot (none : Option tm.Λ) l)) env).2
  apply Prod.ext
  · simp [packedResult, FiniteMachine.result, StatementRows.halt, Rows.renameOutput,
      Rows.seq, Rows.parallel, Rows.route, shift_zero]
  · simpa [Routing.input, packedResult, FiniteMachine.result, StatementRows.halt,
      Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route,
      constant_tabulate_length, shift_zero] using hr

theorem test_eq (env : Address tm C → ℕ) (f : tm.σ → Bool) :
    PrimitiveMachines.test tm f (C, (addresses tm C).map env) =
      (rowBytes (StatementRows.test tm C f env).1, [(StatementRows.test tm C f env).2 ()]) := by
  rw [PrimitiveMachines.test, stateRefs_pack]
  simp [StatementRows.test, Rows.renameOutput, Rows.seq, Rows.route, Rows.renameInput,
    PrimitiveBlocks.stateRoute]

theorem labelTest_eq (env : Address tm C → ℕ) (l : tm.Λ) :
    StatementMachine.labelTest tm l (C, (addresses tm C).map env) =
      ([], [env (labelAddr tm C (some l))]) := by
  unfold StatementMachine.labelTest
  rw [Layout.read_label]

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Exactness
