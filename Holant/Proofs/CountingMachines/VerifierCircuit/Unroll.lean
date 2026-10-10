import Holant.Proofs.CountingMachines.VerifierCircuit.Statement

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Fixed-horizon unfolding with reachable capacity bounds

Ported reference proof. See the task validation reports.

The capacity includes one whole statement's syntactic push budget. Correctness
uses bounds on the actual held run, including when the machine has halted.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Unroll

open Holant.LocalDrafts.CountingHardness

open Turing BitLayout
variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]

def emit : ℕ → Emit (Address tm C) (Address tm C)
  | 0 => Emit.id _
  | t + 1 => Emit.seq (emit t) (Statement.hold tm C)

theorem denotes (t : ℕ) : Emit.Denotes (emit tm C t) ((Statement.holdValue tm C)^[t]) := by
  induction t with
  | zero => exact Emit.route_denotes _
  | succ t ih =>
    have he : (Statement.holdValue tm C)^[t + 1] =
        (fun x => Statement.holdValue tm C ((Statement.holdValue tm C)^[t] x)) := by
      funext x
      exact Function.iterate_succ_apply' _ _ _
    rw [he]
    exact Emit.seq_denotes ih (Statement.hold_denotes tm C)

theorem actual_run (input : List (tm.Γ tm.k₀)) (T : ℕ)
    (hC : input.length + T * VerifierRun.pushBudget tm + VerifierRun.pushBudget tm ≤ C + 1)
    (t : ℕ) (ht : t ≤ T) :
    (Statement.holdValue tm C)^[t] (encode tm C (PackedStep.packRaw tm C (initList tm input))) =
      encode tm C (PackedStep.packRaw tm C ((VerifierRun.holdStep tm)^[t] (initList tm input))) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih (by omega), Statement.hold_encode]
    have hb : ∀ k, (((VerifierRun.holdStep tm)^[t] (initList tm input)).stk k).length +
        VerifierRun.pushBudget tm ≤ C + 1 := by
      intro k
      have hs := VerifierRun.run_stack_bound tm input t k
      have hm := Nat.mul_le_mul_right (VerifierRun.pushBudget tm) (show t ≤ T by omega)
      omega
    rw [PackedStep.hold_correct tm C _ hb, Function.iterate_succ_apply']

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Unroll
