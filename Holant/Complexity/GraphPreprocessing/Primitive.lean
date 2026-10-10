import Holant.Complexity.StackProtocol

/-! Actual accumulated primitive-instruction cost, obtained by executing the
previously verified statement interpreter at every TM2 transition. This is a
machine execution counter, not a cost attached to a semantic graph algorithm. -/
namespace Holant.Complexity.GraphPreprocessing.Primitive
open Turing
variable {K Λ σ : Type} [DecidableEq K]
abbrev Config (K Λ σ : Type) := TM2.Cfg (fun _ : K => Bool) Λ σ
abbrev Program (K Λ σ : Type) := Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

def tick (program : Program K Λ σ) : Option (Config K Λ σ) → ℕ × Option (Config K Λ σ)
  | none => (0, none)
  | some c => match c.l with
    | none => (0, none)
    | some label => let r := TM2Cost.primitiveRun (program label) c.var c.stk; (r.1, some r.2)

def run (program : Program K Λ σ) : ℕ → Option (Config K Λ σ) → ℕ × Option (Config K Λ σ)
  | 0, c => (0, c)
  | n + 1, c => let first := tick program c; let rest := run program n first.2; (first.1 + rest.1, rest.2)

@[simp] theorem tick_result (program : Program K Λ σ) (c : Option (Config K Λ σ)) :
    (tick program c).2 = c.bind (TM2.step program) := by
  cases c with
  | none => rfl
  | some c => cases c with | mk label state tapes => cases label <;> simp [tick, TM2.step]

theorem run_result (program : Program K Λ σ) (n : ℕ) (c : Option (Config K Λ σ)) :
    (run program n c).2 = (fun d => d.bind (TM2.step program))^[n] c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [run, ih, tick_result, Function.iterate_succ_apply]

theorem tick_cost_le (program : Program K Λ σ) (C : ℕ)
    (h : ∀ label, TM2Cost.budget (program label) ≤ C) (c : Option (Config K Λ σ)) :
    (tick program c).1 ≤ C := by
  cases c with
  | none => exact Nat.zero_le C
  | some c =>
    cases hl : c.l with
    | none => simp [tick, hl]
    | some label =>
      simpa only [tick, hl] using
        (le_trans (TM2Cost.primitiveRun_cost_le (program label) c.var c.stk) (h label))

theorem run_cost_le (program : Program K Λ σ) (C : ℕ)
    (h : ∀ label, TM2Cost.budget (program label) ≤ C) (n : ℕ) (c : Option (Config K Λ σ)) :
    (run program n c).1 ≤ C * n := by
  induction n generalizing c with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    dsimp only [run]
    have h₁ := tick_cost_le program C h c
    have h₂ := ih (tick program c).2
    rw [Nat.mul_succ]
    omega

/-- Joint operational endpoint and actual accumulated bit-instruction bound. -/
theorem execution_cost (program : Program K Λ σ) (C : ℕ)
    (hbudget : ∀ label, TM2Cost.budget (program label) ≤ C)
    (n : ℕ) (a b : Config K Λ σ)
    (hexact : (fun d => d.bind (TM2.step program))^[n] (some a) = some b) :
    (run program n (some a)).2 = some b ∧ (run program n (some a)).1 ≤ C * n :=
  ⟨(run_result program n (some a)).trans hexact, run_cost_le program C hbudget n (some a)⟩

end Holant.Complexity.GraphPreprocessing.Primitive
