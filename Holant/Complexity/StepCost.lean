import Holant.Complexity.OracleMachine
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Primitive stack-operation accounting

A TM2 statement is a finite syntax tree. `primitiveRun` independently interprets
that syntax, counting each push, pop, peek, load, branch, goto, or halt once. Its
result equals mathlib `TM2.stepAux`, and its cost is bounded by the statement's
syntax. This justifies a fixed bound on elementary instructions per ordinary
oracle-machine transition; it is not a bit-cost theorem for field operations.
-/

namespace Holant.Complexity

open Turing

namespace TM2Cost

variable {K Γ Λ σ : Type} [DecidableEq K]

/-- A syntax-only upper bound on the executed primitive instructions. -/
def budget : TM2.Stmt (fun _ : K => Γ) Λ σ → ℕ
  | .push _ _ q => budget q + 1
  | .pop _ _ q => budget q + 1
  | .peek _ _ q => budget q + 1
  | .load _ q => budget q + 1
  | .branch _ a b => max (budget a) (budget b) + 1
  | .goto _ => 1
  | .halt => 1

/-- Execute one finite statement and record the actual number of primitive
instructions on the chosen branch, alongside its resulting configuration. -/
def primitiveRun : TM2.Stmt (fun _ : K => Γ) Λ σ → σ → (K → List Γ) →
    ℕ × TM2.Cfg (fun _ : K => Γ) Λ σ
  | .push k f q, v, S =>
    let r := primitiveRun q v (Function.update S k (f v :: S k))
    (r.1 + 1, r.2)
  | .pop k f q, v, S =>
    let r := primitiveRun q (f v (S k).head?) (Function.update S k (S k).tail)
    (r.1 + 1, r.2)
  | .peek k f q, v, S =>
    let r := primitiveRun q (f v (S k).head?) S
    (r.1 + 1, r.2)
  | .load f q, v, S =>
    let r := primitiveRun q (f v) S
    (r.1 + 1, r.2)
  | .branch f a b, v, S =>
    let r := if f v then primitiveRun a v S else primitiveRun b v S
    (r.1 + 1, r.2)
  | .goto f, v, S => (1, ⟨some (f v), v, S⟩)
  | .halt, v, S => (1, ⟨none, v, S⟩)

/-- The instrumented interpreter returns exactly the library's statement result. -/
@[simp] theorem primitiveRun_result (q : TM2.Stmt (fun _ : K => Γ) Λ σ)
    (v : σ) (S : K → List Γ) : (primitiveRun q v S).2 = TM2.stepAux q v S := by
  induction q generalizing v S with
  | push k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f a b ha hb =>
    cases h : f v <;> simp [primitiveRun, TM2.stepAux, h, ha, hb]
  | goto f => rfl
  | halt => rfl

/-- Runtime cost is bounded by fixed program syntax, not by stack contents. -/
theorem primitiveRun_cost_le (q : TM2.Stmt (fun _ : K => Γ) Λ σ)
    (v : σ) (S : K → List Γ) : (primitiveRun q v S).1 ≤ budget q := by
  induction q generalizing v S with
  | push k f q ih => exact Nat.add_le_add_right (ih _ _) 1
  | pop k f q ih => exact Nat.add_le_add_right (ih _ _) 1
  | peek k f q ih => exact Nat.add_le_add_right (ih _ _) 1
  | load f q ih => exact Nat.add_le_add_right (ih _ _) 1
  | branch f a b ha hb =>
    cases h : f v
    · simpa [primitiveRun, budget, h] using
        Nat.add_le_add_right (le_trans (hb v S) (le_max_right (budget a) (budget b))) 1
    · simpa [primitiveRun, budget, h] using
        Nat.add_le_add_right (le_trans (ha v S) (le_max_left (budget a) (budget b))) 1
  | goto f => exact Nat.le_refl _
  | halt => exact Nat.le_refl _

end TM2Cost

namespace OracleMachine

/-- A safe bound for one command at a given control label. A query is one oracle
operation; every ordinary statement receives its syntax bound. -/
def commandBudget (m : OracleMachine) (label : m.Λ) : ℕ :=
  match m.program label with
  | .ordinary q => TM2Cost.budget q
  | .query _ => 1

/-- Since control labels are finite, one fixed number bounds all command costs. -/
def primitiveBudget (m : OracleMachine) : ℕ := ∑ label, m.commandBudget label

theorem commandBudget_le (m : OracleMachine) (label : m.Λ) :
    m.commandBudget label ≤ m.primitiveBudget := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ label)

/-- Every actual ordinary-command execution obeys the fixed machine bound. -/
theorem ordinary_cost_le (m : OracleMachine) (label : m.Λ)
    (q : TM2.Stmt (fun _ : m.K => Bool) m.Λ m.σ)
    (h : m.program label = .ordinary q) (v : m.σ) (S : m.K → List Bool) :
    (TM2Cost.primitiveRun q v S).1 ≤ m.primitiveBudget := by
  apply le_trans (TM2Cost.primitiveRun_cost_le q v S)
  simpa [commandBudget, h] using m.commandBudget_le label

end OracleMachine
end Holant.Complexity
