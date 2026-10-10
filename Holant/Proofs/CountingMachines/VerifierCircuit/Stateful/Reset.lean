import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.StatementRows

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Canonical post-round references and exact steady-block repetition

Ported reference proof. See the task validation reports.

The outer dispatch is nonempty because the real machine has `main`. Its final
tabulation emits four gates for every address. This resets *wire references*,
not Boolean values: every later held-step block has literally identical rows.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Reset


open Turing BitLayout
open scoped Classical
variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]

local instance addressBEq : BEq (Address tm C) := instBEqOfDecidableEq

def references (a : Address tm C) : ℕ :=
  4 * ((addresses tm C).length - ((addresses tm C).idxOf a + 1))

theorem choose_output (t : Rows.Run (Address tm C) Unit)
    (p q : Rows.Run (Address tm C) (Address tm C)) (env : Address tm C → ℕ) :
    (StatementRows.choose tm C t p q env).2 = references tm C := by
  funext a
  have h := Rows.tabulate_output (addresses tm C) (mem_addresses tm C)
    (fun a => Rows.mux (.inl ()) (.inr (.inl a)) (.inr (.inr a))) (fun _ => 4)
    (fun _ _ => Rows.mux_length _ _ _ _) (fun _ _ => Rows.mux_output _ _ _ _ ())
    ((Rows.parallel t (Rows.parallel p q) env).2) a
  simpa [StatementRows.choose, Rows.seq, references, Nat.mul_comm] using h

theorem labels_nonempty : fixedEnum tm.Λ ≠ [] := by
  intro h
  have hm := mem_fixedEnum tm.main
  rw [h] at hm
  exact List.not_mem_nil hm

theorem hold_output (env : Address tm C → ℕ) :
    (StatementRows.hold tm C env).2 = references tm C := by
  unfold StatementRows.hold
  cases h : fixedEnum tm.Λ with
  | nil => exact False.elim (labels_nonempty tm h)
  | cons l ls => exact choose_output tm C _ _ _ env

theorem unroll_output (T : ℕ) (env : Address tm C → ℕ) :
    (StatementRows.unroll tm C (T + 1) env).2 = references tm C :=
  hold_output tm C _

def steadyRows : List Circuit.Row := (StatementRows.hold tm C (references tm C)).1

/-- This is an equality of row lists in the existing newest-register-first
encoding. No renumbering by the accumulated global gate count is needed after
the first round: all retained references have been reset by its last mux block. -/
theorem unroll_rows (T : ℕ) (env : Address tm C → ℕ) :
    (StatementRows.unroll tm C (T + 1) env).1 =
      (StatementRows.hold tm C env).1 ++ (List.replicate T (steadyRows tm C)).flatten := by
  induction T with
  | zero => simp [StatementRows.unroll, Rows.seq, Rows.route]
  | succ T ih =>
    change (StatementRows.unroll tm C (T + 1) env).1 ++
      (StatementRows.hold tm C (StatementRows.unroll tm C (T + 1) env).2).1 = _
    rw [unroll_output, ih]
    simp [steadyRows, List.replicate_succ', List.flatten_append, List.append_assoc]

/-- Direct link back to `Unroll.emit`, including the final live-reference
values. The caller supplies only actual input wires, not a row-correctness
certificate. -/
theorem exact_unroll (A : Type) (n : ℕ) (ctx : A → Fin n)
    (input : Address tm C → Fin n) (T : ℕ) :
    ∃ (m : ℕ) (ctx' : A → Fin m) (out : Address tm C → Fin m),
      (∀ a, (out a).val = references tm C a) ∧
      ∀ k : Continuation A (Address tm C),
        (Unroll.emit tm C (T + 1) ctx input k).code =
          Rows.«prefix» ((StatementRows.hold tm C (fun a => (input a).val)).1 ++
            (List.replicate T (steadyRows tm C)).flatten) (k ctx' out).code := by
  obtain ⟨m, ctx', out, hm, hc, ho, he⟩ := StatementRows.unroll_exact tm C (T + 1) A n ctx input
  refine ⟨m, ctx', out, ?_, ?_⟩
  · intro a
    rw [ho, unroll_output]
  · intro k
    simpa only [unroll_rows] using he k

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Reset
