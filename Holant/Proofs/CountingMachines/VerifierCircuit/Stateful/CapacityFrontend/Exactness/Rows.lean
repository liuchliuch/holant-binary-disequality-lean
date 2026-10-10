import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.Frontend

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

Exact list facts needed to identify the already implemented frontend. No new
compiler or machine is defined here. Constant blocks include their real suffix
indices, and canonical arrays are compared as whole ordered lists.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Exactness


open Turing BitLayout OutputMachine
open scoped Classical

theorem shift_map {I : Type} (g : ℕ) (xs : List I) (env : I → ℕ) :
    Environment.shift g (xs.map env) = xs.map (Rows.shift g env) :=
  Environment.shift_pack g xs env

theorem shift_add {I : Type} (g h : ℕ) (env : I → ℕ) :
    Rows.shift h (Rows.shift g env) = Rows.shift (g + h) env := by
  funext i
  simp [Rows.shift, Nat.add_assoc]

theorem shift_zero {I : Type} (env : I → ℕ) : Rows.shift 0 env = env := by
  funext i
  simp [Rows.shift]

theorem constant_gather_rows {I O : Type} (bits : O → Bool) (xs : List O) (env : I → ℕ) :
    (Rows.gather (fun o => Rows.constant (bits o)) xs env).1 =
      xs.map (fun o => (if bits o then 1 else 0, (0, 0))) := by
  induction xs generalizing env with
  | nil => rfl
  | cons o xs ih =>
    simp [Rows.gather, Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route,
      Rows.constant, ih]

theorem constant_tabulate {I O : Type} [DecidableEq O] (bits : O → Bool)
    (xs : List O) (covers : ∀ o, o ∈ xs) (env : I → ℕ) :
    Rows.tabulate xs covers (fun o => Rows.constant (bits o)) env =
      (xs.map (fun o => (if bits o then 1 else 0, (0, 0))),
        fun o => xs.length - (xs.idxOf o + 1)) := by
  apply Prod.ext
  · simpa [Rows.tabulate, Rows.renameOutput, Rows.seq, Rows.route] using
      constant_gather_rows bits xs env
  · funext o
    have h := Rows.tabulate_output xs covers (fun o => Rows.constant (bits o)) (fun _ => 1)
      (fun _ _ => rfl) (fun _ _ => rfl) env o
    simpa using h

theorem constant_tabulate_independent {I J O : Type} [DecidableEq O] (bits : O → Bool)
    (xs : List O) (covers : ∀ o, o ∈ xs) (env : I → ℕ) (other : J → ℕ) :
    Rows.tabulate xs covers (fun o => Rows.constant (bits o)) env =
      Rows.tabulate xs covers (fun o => Rows.constant (bits o)) other := by
  rw [constant_tabulate, constant_tabulate]

theorem constant_tabulate_length {I O : Type} [DecidableEq O] (bits : O → Bool)
    (xs : List O) (covers : ∀ o, o ∈ xs) (env : I → ℕ) :
    (Rows.tabulate xs covers (fun o => Rows.constant (bits o)) env).1.length = xs.length := by
  rw [constant_tabulate]
  exact List.length_map _

theorem table₂_length {I O P : Type} [Fintype I] [Fintype O] [Fintype P]
    [DecidableEq I] [DecidableEq O] [DecidableEq P]
    (f : I → O → P) (env : I ⊕ O → ℕ) :
    (Rows.table₂ f env).1.length = Emit.table₂Cost f := by
  have hc : (Rows.cross (A := I) (B := O) env).1.length = 2 * Fintype.card (I × O) := by
    have h := Rows.gather_length (fun ab : I × O => Rows.and (.inl ab.1) (.inr ab.2))
      (fun _ => 2) (fun _ _ => rfl) (fixedEnum (I × O)) env
    simpa [Rows.cross, Rows.tabulate, Rows.renameOutput, Rows.seq, Rows.route, Nat.mul_comm] using h
  simp only [Rows.table₂, Rows.seq, List.length_append, hc, PrimitiveMachines.table_length,
    Emit.table₂Cost]

theorem mux_tabulate_length {I O : Type} [DecidableEq O] (xs : List O)
    (covers : ∀ o, o ∈ xs) (s t e : O → I) (env : I → ℕ) :
    (Rows.tabulate xs covers (fun o => Rows.mux (s o) (t o) (e o)) env).1.length = 4 * xs.length := by
  have h := Rows.gather_length (fun o => Rows.mux (s o) (t o) (e o)) (fun _ => 4)
    (fun _ _ => Rows.mux_length _ _ _ _) xs env
  simpa [Rows.tabulate, Rows.renameOutput, Rows.seq, Rows.route, Nat.mul_comm] using h

theorem triples_map {I : Type} (xs : List I) (s : ℕ) (yes no : I → ℕ) :
    StatementMachine.chooseTriples s (xs.map yes) (xs.map no) xs.length =
      xs.map (fun i => (s, yes i, no i)) := by
  apply List.ext_getElem
  · simp [StatementMachine.chooseTriples]
  · intro i hi hj
    have h : i < xs.length := by simpa using hj
    simp [StatementMachine.chooseTriples, List.getElem?_eq_getElem h]

variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]

local instance addressBEq : BEq (Address tm C) := instBEqOfDecidableEq

theorem canonical_pack : CanonicalMachine.values (addresses tm C).length =
    (addresses tm C).map (Reset.references tm C) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < (addresses tm C).length := by simpa using hj
    have hc := CanonicalMachine.get_value (addresses tm C).length ⟨i, h⟩
    have hx := (Layout.addresses_nodup tm C).idxOf_getElem i h
    simpa [List.get_eq_getElem, Reset.references, hx] using hc

theorem width_eq (env : List ℕ) : StatementMachine.width tm (C, env) = (addresses tm C).length :=
  (addresses_length tm C).symm

theorem load_length (f : tm.σ → tm.σ) (env : Address tm C → ℕ) :
    (StatementRows.load tm C f env).1.length = Emit.tableCost f := by
  simp [StatementRows.load, Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route,
    Rows.renameInput, PrimitiveMachines.table_length]

theorem readState_length (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) (env : Address tm C → ℕ) :
    (StatementRows.readState tm C k f env).1.length = Emit.table₂Cost f := by
  simp [StatementRows.readState, Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route,
    Rows.renameInput, table₂_length]

theorem push_length (k : tm.K) (f : tm.σ → tm.Γ k) (env : Address tm C → ℕ) :
    (StatementRows.push tm C k f env).1.length = Emit.tableCost (fun s => some (f s)) := by
  simp [StatementRows.push, Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route,
    Rows.renameInput, PrimitiveMachines.table_length]

theorem pop_length (k : tm.K) (env : Address tm C → ℕ) :
    (StatementRows.pop tm C k env).1.length = Fintype.card (Option (tm.Γ k)) := by
  simp only [StatementRows.pop, Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route,
    List.nil_append, List.append_nil, shift_zero]
  simpa using constant_tabulate_length (oneHot (none : Option (tm.Γ k)))
    (fixedEnum (Option (tm.Γ k))) mem_fixedEnum env

theorem goto_length (f : tm.σ → tm.Λ) (env : Address tm C → ℕ) :
    (StatementRows.goto tm C f env).1.length = Emit.tableCost (fun s => some (f s)) := by
  simp [StatementRows.goto, Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route,
    Rows.renameInput, PrimitiveMachines.table_length]

theorem halt_length (env : Address tm C → ℕ) :
    (StatementRows.halt tm C env).1.length = Fintype.card (Option tm.Λ) := by
  simp only [StatementRows.halt, Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route,
    List.nil_append, List.append_nil, shift_zero]
  simpa using constant_tabulate_length (oneHot (none : Option tm.Λ))
    (fixedEnum (Option tm.Λ)) mem_fixedEnum env

theorem test_length (f : tm.σ → Bool) (env : Address tm C → ℕ) :
    (StatementRows.test tm C f env).1.length = Emit.tableCost f := by
  simp [StatementRows.test, Rows.renameOutput, Rows.seq, Rows.route, Rows.renameInput,
    PrimitiveMachines.table_length]

theorem choose_length (t : Rows.Run (Address tm C) Unit)
    (p q : Rows.Run (Address tm C) (Address tm C)) (env : Address tm C → ℕ) :
    (StatementRows.choose tm C t p q env).1.length =
      (t env).1.length +
        ((p (Rows.shift (t env).1.length env)).1.length +
          (q (Rows.shift (p (Rows.shift (t env).1.length env)).1.length
            (Rows.shift (t env).1.length env))).1.length) + 4 * (addresses tm C).length := by
  simp only [StatementRows.choose, Rows.seq, Rows.parallel, List.length_append,
    mux_tabulate_length]

theorem statement_length (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (env : Address tm C → ℕ) :
    (StatementRows.statement tm C q env).1.length = GateCost.statement tm C q := by
  induction q generalizing env with
  | push k f q ih => simp [StatementRows.statement, Rows.seq, push_length, ih, GateCost.statement]
  | pop k f q ih => simp [StatementRows.statement, Rows.seq, readState_length, pop_length, ih, GateCost.statement]
  | peek k f q ih => simp [StatementRows.statement, Rows.seq, readState_length, ih, GateCost.statement]
  | load f q ih => simp [StatementRows.statement, Rows.seq, load_length, ih, GateCost.statement]
  | branch f q r ihq ihr =>
    simp [StatementRows.statement, choose_length, test_length, ihq, ihr,
      GateCost.statement, GateCost.width]
  | goto f => exact goto_length tm C f env
  | halt => exact halt_length tm C env

theorem dispatch_length (ls : List tm.Λ) (env : Address tm C → ℕ) :
    (StatementRows.dispatch tm C ls env).1.length = GateCost.dispatch tm C ls := by
  induction ls generalizing env with
  | nil => rfl
  | cons l ls ih =>
    simp [StatementRows.dispatch, choose_length, statement_length, ih,
      Rows.route, GateCost.dispatch, GateCost.width]

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Exactness
