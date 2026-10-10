import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.Exactness.Primitives

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

Exact saved references, mux records, and induction over the existing statement
and dispatch programs. The final statement/dispatch/hold equalities have no
correctness premises. Private composition lemmas discharge only the induction
hypotheses for proper subprograms, using the independently proved row lengths.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Exactness


open Turing BitLayout OutputMachine PrimitiveMachines
open scoped Classical

variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]

/-- The three saved wires after both arms have been emitted, before the mux
batch. Both shifts come from actual emitted row lengths. -/
theorem choose_result (t : Rows.Run (Address tm C) Unit)
    (p q : Rows.Run (Address tm C) (Address tm C)) (env : Address tm C → ℕ) :
    let first := t env
    let left := p (Rows.shift first.1.length env)
    let right := q (Rows.shift left.1.length (Rows.shift first.1.length env))
    (rowBytes first.1 ++ (rowBytes left.1 ++ (rowBytes right.1 ++
      rowBytes (MuxMachine.batchRecords (StatementMachine.chooseTriples
        (first.2 () + (left.1.length + right.1.length))
        (Environment.shift right.1.length ((addresses tm C).map left.2))
        ((addresses tm C).map right.2) (addresses tm C).length)))),
      CanonicalMachine.values (addresses tm C).length) =
        packedResult tm C (StatementRows.choose tm C t p q env) := by
  dsimp only
  apply Prod.ext
  · simp only [packedResult, StatementRows.choose, Rows.seq]
    rw [rowBytes_append, MuxMachine.tabulate_rows]
    rw [shift_map, triples_map]
    simp [Rows.parallel, Rows.shift, rowBytes_append, List.append_assoc]
  · simp only [packedResult, Reset.choose_output]
    exact canonical_pack tm C

private theorem seq_eq (left right : Input → Output)
    (p q : Rows.Run (Address tm C) (Address tm C))
    (hp : ∀ env, left (C, (addresses tm C).map env) = packedResult tm C (p env))
    (hq : ∀ env, right (C, (addresses tm C).map env) = packedResult tm C (q env))
    (env : Address tm C → ℕ) :
    StatementMachine.seq left right (C, (addresses tm C).map env) =
      packedResult tm C (Rows.seq p q env) := by
  simp [StatementMachine.seq, hp, hq, packedResult, Rows.seq, rowBytes_append]

private theorem choose_eq (ct cp cq : ℕ → ℕ) (test yes no : Input → Output)
    (t : Rows.Run (Address tm C) Unit) (p q : Rows.Run (Address tm C) (Address tm C))
    (ht : ∀ env, test (C, (addresses tm C).map env) = (rowBytes (t env).1, [(t env).2 ()]))
    (hp : ∀ env, yes (C, (addresses tm C).map env) = packedResult tm C (p env))
    (hq : ∀ env, no (C, (addresses tm C).map env) = packedResult tm C (q env))
    (hct : ∀ env, (t env).1.length = ct C)
    (hcp : ∀ env, (p env).1.length = cp C)
    (hcq : ∀ env, (q env).1.length = cq C)
    (env : Address tm C → ℕ) :
    StatementMachine.choose tm ct cp cq test yes no (C, (addresses tm C).map env) =
      packedResult tm C (StatementRows.choose tm C t p q env) := by
  have h := choose_result tm C t p q env
  simpa [StatementMachine.choose, StatementMachine.shiftInput, shift_map, ht, hp, hq,
    packedResult, hct, hcp, hcq, shift_add, width_eq] using h

theorem statement_eq (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (env : Address tm C → ℕ) :
    StatementMachine.statement tm q (C, (addresses tm C).map env) =
      packedResult tm C (StatementRows.statement tm C q env) := by
  induction q generalizing env with
  | push k f q ih =>
    exact seq_eq tm C _ _ _ _ (fun env => push_eq tm C env k f) ih env
  | pop k f q ih =>
    exact seq_eq tm C _ _ _ _ (fun env => readState_eq tm C env k f)
      (fun env => seq_eq tm C _ _ _ _ (fun env => pop_eq tm C env k) ih env) env
  | peek k f q ih =>
    exact seq_eq tm C _ _ _ _ (fun env => readState_eq tm C env k f) ih env
  | load f q ih =>
    exact seq_eq tm C _ _ _ _ (fun env => PrimitiveMachines.load_eq tm C env f) ih env
  | branch f q r ihq ihr =>
    exact choose_eq tm C _ _ _ _ _ _ _ _ _ (fun env => test_eq tm C env f) ihq ihr
      (fun env => test_length tm C f env)
      (fun env => statement_length tm C q env)
      (fun env => statement_length tm C r env) env
  | goto f => exact goto_eq tm C env f
  | halt => exact halt_eq tm C env

theorem dispatch_eq (ls : List tm.Λ) (env : Address tm C → ℕ) :
    StatementMachine.dispatch tm ls (C, (addresses tm C).map env) =
      packedResult tm C (StatementRows.dispatch tm C ls env) := by
  induction ls generalizing env with
  | nil => rfl
  | cons l ls ih =>
    exact choose_eq tm C _ _ _ _ _ _ _ _ _
      (fun env => labelTest_eq tm C env l)
      (fun env => statement_eq tm C (tm.m l) env) ih
      (fun _ => rfl) (fun env => statement_length tm C (tm.m l) env)
      (fun env => dispatch_length tm C ls env) env

/-- The contract's complete ordered-row and live-reference equality. -/
theorem hold_eq (env : Address tm C → ℕ) :
    StatementMachine.dispatch tm (fixedEnum tm.Λ) (C, (addresses tm C).map env) =
      packedResult tm C (StatementRows.hold tm C env) :=
  dispatch_eq tm C (fixedEnum tm.Λ) env

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Exactness
