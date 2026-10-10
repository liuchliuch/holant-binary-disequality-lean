import Holant.Complexity.OracleMachine
import Holant.Complexity.OutputSize

/-!
# Valid, polynomial-length oracle queries and answers

Unit-cost oracle answers need explicit word-length control before a composition
simulation can be sound. This module verifies that control against actual runs,
requires every query to be a valid encoded target input, and derives one polynomial
bound for every answer encountered. Reflexivity has a concrete verified certificate.
The general oracle-machine inlining/composition construction is not yet proved.
-/

namespace Holant.Complexity

open Computability

/-- Natural-coefficient polynomial bounds are monotone on natural input lengths. -/
theorem natPolynomial_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

namespace OracleMachine

/-- Execute exactly `t` actual transitions, retaining divergence past a halt as `none`. -/
def run (m : OracleMachine) (oracle : List Bool → List Bool) (input : List Bool) (t : ℕ) :
    Option m.Cfg :=
  (fun c : Option m.Cfg => c.bind (m.step oracle))^[t] (some (m.init input))

@[simp] theorem run_zero (m : OracleMachine) (oracle : List Bool → List Bool) (input : List Bool) :
    m.run oracle input 0 = some (m.init input) := rfl

theorem run_succ (m : OracleMachine) (oracle : List Bool → List Bool) (input : List Bool) (t : ℕ) :
    m.run oracle input (t + 1) = (m.run oracle input t).bind (m.step oracle) :=
  Function.iterate_succ_apply' _ _ _

/-- A query is determined solely by the active program command. -/
def IsQuery (m : OracleMachine) (c : m.Cfg) : Prop :=
  ∃ label next, c.l = some label ∧ m.program label = .query next

end OracleMachine

/-- Polynomial-time reduction plus actual-run query validity/length proofs and
an independently proved output-size bound for the target function. -/
structure LengthControlledOracleReduction {α β γ δ : Type}
    (ea : Encoding α Bool) (eb : Encoding β Bool)
    (ec : Encoding γ Bool) (ed : Encoding δ Bool) (f : α → β) (g : γ → δ) where
  reduction : PolyTimeOracleReduction ea eb ec ed f g
  targetOutput : PolynomialOutputBound ec ed g
  queryBound : Polynomial ℕ
  safeQuery : ∀ oracle, RepresentsOracle ec ed g oracle → ∀ a t c,
    reduction.machine.run oracle (ea.encode a) t = some c → reduction.machine.IsQuery c →
    ∃ q, c.stk reduction.machine.queryStack = ec.encode q ∧
      (c.stk reduction.machine.queryStack).length ≤ queryBound.eval (ea.encode a).length

namespace LengthControlledOracleReduction

variable {α β γ δ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f : α → β} {g : γ → δ}

/-- Every answer encountered on an actual run has a polynomial bit-length bound
in the original source input, even though receiving it is one oracle transition. -/
theorem answer_length_le (r : LengthControlledOracleReduction ea eb ec ed f g)
    (oracle : List Bool → List Bool) (h : RepresentsOracle ec ed g oracle)
    (a : α) (t : ℕ) (c : r.reduction.machine.Cfg)
    (hrun : r.reduction.machine.run oracle (ea.encode a) t = some c)
    (hq : r.reduction.machine.IsQuery c) :
    (oracle (c.stk r.reduction.machine.queryStack)).length ≤
      (r.targetOutput.bound.comp r.queryBound).eval (ea.encode a).length := by
  obtain ⟨q, he, hlen⟩ := r.safeQuery oracle h a t c hrun hq
  rw [he, h q, Polynomial.eval_comp]
  apply le_trans (r.targetOutput.length_le q)
  apply natPolynomial_eval_mono
  simpa [he] using hlen

end LengthControlledOracleReduction

/-- The one-query machine's sole query command is its initial label. -/
theorem queryOnce_isQuery_iff (c : queryOnceMachine.Cfg) :
    queryOnceMachine.IsQuery c ↔ c.l = some false := by
  constructor
  · rintro ⟨label, next, hlabel, hcommand⟩
    cases label with
    | false => exact hlabel
    | true => simp [queryOnceMachine] at hcommand
  · intro h
    exact ⟨false, (fun _ => true), h, rfl⟩

/-- No actual transition of the one-query machine can re-enter its query label. -/
theorem queryOnce_step_not_query (oracle : List Bool → List Bool) (c : queryOnceMachine.Cfg) :
    ((queryOnceMachine.step oracle c).map (fun d => d.l)) ≠ some (some false) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => simp [OracleMachine.step]
  | some label => cases label <;> simp [OracleMachine.step, queryOnceMachine, Turing.TM2.stepAux]

/-- Every query in a run is exactly the untouched initial query. -/
theorem queryOnce_query_is_initial (oracle : List Bool → List Bool) (input : List Bool)
    (t : ℕ) (c : queryOnceMachine.Cfg)
    (hrun : queryOnceMachine.run oracle input t = some c) (hq : queryOnceMachine.IsQuery c) :
    c = queryOnceMachine.init input := by
  cases t with
  | zero => exact (Option.some.inj hrun).symm
  | succ t =>
    rw [OracleMachine.run_succ] at hrun
    cases hp : queryOnceMachine.run oracle input t with
    | none => simp [hp] at hrun
    | some previous =>
      have hs : queryOnceMachine.step oracle previous = some c := by simpa [hp] using hrun
      have hnot := queryOnce_step_not_query oracle previous
      rw [hs] at hnot
      exact False.elim (hnot (congrArg some ((queryOnce_isQuery_iff c).mp hq)))

/-- Nonvacuous controlled reflexivity for any target with a proved polynomial
output bound, including the #P and fixed-field bounds established elsewhere. -/
noncomputable def lengthControlled_refl {α β : Type} (ea : Encoding α Bool)
    (eb : Encoding β Bool) (f : α → β) (hOutput : PolynomialOutputBound ea eb f) :
    LengthControlledOracleReduction ea eb ea eb f f := by
  refine ⟨oracleReduction_refl ea eb f, hOutput, Polynomial.X, ?_⟩
  intro oracle h a t c hrun hq
  have hc := queryOnce_query_is_initial oracle (ea.encode a) t c hrun hq
  subst c
  refine ⟨a, ?_, ?_⟩ <;> simp [OracleMachine.init, queryOnceMachine]

end Holant.Complexity
