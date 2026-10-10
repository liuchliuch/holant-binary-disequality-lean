import Holant.Complexity.OracleQueryBounds
import Holant.Complexity.StepCost

/-!
# Actual stack-space and output bounds for controlled oracle reductions

Ordinary instructions can grow stacks only by their explicit pushes. Oracle calls
can grow them only by a proved answer-length bound. Induction over actual machine
transitions therefore bounds every intermediate stack and the final output by an
explicit polynomial. No space annotation is trusted independently of execution.
-/

namespace Holant.Complexity

open Turing
open scoped BigOperators

/-- Total stored bits over the actual finite collection of binary stacks. -/
def stackSize {K : Type} [Fintype K] (S : K → List Bool) : ℕ := ∑ k, (S k).length

/-- Replacing one stack adds at most the allowed increase to total stored bits. -/
theorem stackSize_update_le {K : Type} [Fintype K] [DecidableEq K]
    (S : K → List Bool) (k : K) (word : List Bool) (B : ℕ)
    (h : word.length ≤ (S k).length + B) :
    stackSize (Function.update S k word) ≤ stackSize S + B := by
  calc
    stackSize (Function.update S k word) ≤
        ∑ i, ((S i).length + if i = k then B else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i = k
      · subst i
        simpa using h
      · simp [hi]
    _ = stackSize S + B := by simp [stackSize, Finset.sum_add_distrib]

namespace TM2Cost

/-- Actual stack growth of one finite TM2 statement is bounded by its syntax. -/
theorem stepAux_size_le {K Λ σ : Type} [Fintype K] [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (S : K → List Bool) :
    stackSize (TM2.stepAux q v S).stk ≤ stackSize S + budget q := by
  induction q generalizing v S with
  | push k f q ih =>
    have hs := stackSize_update_le S k (f v :: S k) 1 (by simp)
    have hh := ih v (Function.update S k (f v :: S k))
    change stackSize (TM2.stepAux q v (Function.update S k (f v :: S k))).stk ≤ _
    simp only [budget]
    omega
  | pop k f q ih =>
    have hs := stackSize_update_le S k (S k).tail 0 (by simp)
    have hh := ih (f v (S k).head?) (Function.update S k (S k).tail)
    change stackSize (TM2.stepAux q (f v (S k).head?) (Function.update S k (S k).tail)).stk ≤ _
    simp only [budget]
    omega
  | peek k f q ih =>
    have hh := ih (f v (S k).head?) S
    change stackSize (TM2.stepAux q (f v (S k).head?) S).stk ≤ _
    simp only [budget]
    omega
  | load f q ih =>
    have hh := ih (f v) S
    change stackSize (TM2.stepAux q (f v) S).stk ≤ _
    simp only [budget]
    omega
  | branch f a b ha hb =>
    cases hv : f v
    · simp only [TM2.stepAux, hv, Bool.cond_false, budget]
      have hh := hb v S
      have hm := le_max_right (budget a) (budget b)
      omega
    · simp only [TM2.stepAux, hv, Bool.cond_true, budget]
      have hh := ha v S
      have hm := le_max_left (budget a) (budget b)
      omega
  | goto f => simp [TM2.stepAux, budget]
  | halt => simp [TM2.stepAux, budget]

end TM2Cost

namespace OracleMachine

@[simp] theorem stackSize_init (m : OracleMachine) (input : List Bool) :
    stackSize (m.init input).stk = input.length := by
  simp [stackSize, init, apply_ite]

@[simp] theorem stackSize_output (m : OracleMachine) (value : List Bool) :
    stackSize (m.output value).stk = value.length := by
  simp [stackSize, output, apply_ite]

/-- One actual oracle-machine step respects primitive and oracle-answer growth. -/
theorem step_size_le (m : OracleMachine) (oracle : List Bool → List Bool) (A : ℕ)
    (c d : m.Cfg) (hs : m.step oracle c = some d)
    (ha : m.IsQuery c → (oracle (c.stk m.queryStack)).length ≤ A) :
    stackSize d.stk ≤ stackSize c.stk + m.primitiveBudget + A := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => simp [step] at hs
  | some label =>
    cases hp : m.program label with
    | ordinary q =>
      have hd : TM2.stepAux q state tapes = d := by simpa [step, hp] using hs
      subst d
      have hb : TM2Cost.budget q ≤ m.primitiveBudget := by
        simpa [commandBudget, hp] using m.commandBudget_le label
      have hg := TM2Cost.stepAux_size_le q state tapes
      dsimp only
      omega
    | query next =>
      have hq : m.IsQuery ⟨some label, state, tapes⟩ := ⟨label, next, rfl, hp⟩
      have hanswer := ha hq
      have hd : (⟨some (next state), state,
        Function.update tapes m.answerStack (oracle (tapes m.queryStack))⟩ : m.Cfg) = d := by
        simpa [step, hp] using hs
      subst d
      have hg := stackSize_update_le tapes m.answerStack (oracle (tapes m.queryStack)) A
        (le_trans hanswer (Nat.le_add_left _ _))
      dsimp only at *
      omega

end OracleMachine

namespace LengthControlledOracleReduction

open Computability

variable {α β γ δ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f : α → β} {g : γ → δ}

/-- Every intermediate configuration satisfies the bound, by transition induction. -/
theorem run_stackSize_le (r : LengthControlledOracleReduction ea eb ec ed f g)
    (oracle : List Bool → List Bool) (h : RepresentsOracle ec ed g oracle)
    (a : α) (t : ℕ) (c : r.reduction.machine.Cfg)
    (hr : r.reduction.machine.run oracle (ea.encode a) t = some c) :
    stackSize c.stk ≤ (ea.encode a).length + t * (r.reduction.machine.primitiveBudget +
      (r.targetOutput.bound.comp r.queryBound).eval (ea.encode a).length) := by
  induction t generalizing c with
  | zero =>
    have hc : r.reduction.machine.init (ea.encode a) = c := Option.some.inj hr
    subst c
    simp
  | succ t ih =>
    rw [OracleMachine.run_succ] at hr
    cases hp : r.reduction.machine.run oracle (ea.encode a) t with
    | none => simp [hp] at hr
    | some previous =>
      have hs : r.reduction.machine.step oracle previous = some c := by simpa [hp] using hr
      have hprev := ih previous hp
      have hstep := r.reduction.machine.step_size_le oracle
        ((r.targetOutput.bound.comp r.queryBound).eval (ea.encode a).length) previous c hs
        (fun hq => r.answer_length_le oracle h a t previous hp hq)
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- Ordinary growth plus bounded oracle answers gives an explicit source-output
polynomial, rather than needing that bound as another assumption. -/
noncomputable def sourceOutputPolynomial (r : LengthControlledOracleReduction ea eb ec ed f g) :
    Polynomial ℕ :=
  Polynomial.X + r.reduction.time * (Polynomial.C r.reduction.machine.primitiveBudget +
    r.targetOutput.bound.comp r.queryBound)

theorem source_output_length_le (r : LengthControlledOracleReduction ea eb ec ed f g) (a : α) :
    (eb.encode (f a)).length ≤ r.sourceOutputPolynomial.eval (ea.encode a).length := by
  let oracle := encodedOracle ec ed g
  have ho := encodedOracle_represents ec ed g
  let computation := r.reduction.correct oracle ho a
  have hr : r.reduction.machine.run oracle (ea.encode a) computation.steps =
      some (r.reduction.machine.output (eb.encode (f a))) := computation.evals_in_steps
  have hsize := r.run_stackSize_le oracle ho a computation.steps _ hr
  rw [OracleMachine.stackSize_output] at hsize
  have ht := Nat.mul_le_mul_right (r.reduction.machine.primitiveBudget +
    (r.targetOutput.bound.comp r.queryBound).eval (ea.encode a).length) computation.steps_le_m
  simp only [sourceOutputPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

/-- The resulting output-bound certificate is derived from the actual finite
machine run and its primitive stack semantics. -/
noncomputable def sourceOutputBound (r : LengthControlledOracleReduction ea eb ec ed f g) :
    PolynomialOutputBound ea eb f where
  bound := r.sourceOutputPolynomial
  length_le := r.source_output_length_le

end LengthControlledOracleReduction
end Holant.Complexity
