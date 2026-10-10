import Holant.Complexity.OracleSpace
import Holant.Complexity.OracleCompose

/-!
# Encoded polynomial-time oracle reduction composition

The caller's actual reachable query and answer words control the cost of the
finite inlining protocol. In particular, the old answer stack is bounded from
the proved transition semantics, rather than by an unproved space annotation.
The resulting reduction uses the actual finite compiled oracle machine. Only
the first reduction needs length control; the second needs correctness and its
polynomial time bound.
-/

namespace Holant.Complexity

open Computability

/-- Any individual binary stack is bounded by the total stored bits. -/
theorem stack_length_le_stackSize {K : Type} [Fintype K] (S : K → List Bool) (k : K) :
    (S k).length ≤ stackSize S := by
  unfold stackSize
  exact Finset.single_le_sum (f := fun i => (S i).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

namespace LengthControlledOracleReduction

variable {α β γ δ ε ζ : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool}
  {ee : Encoding ε Bool} {ef : Encoding ζ Bool}
  {f : α → β} {g : γ → δ} {h : ε → ζ}

/-- At every prefix within the certified time, the source-output polynomial
also bounds every actual intermediate stack, including a stale oracle answer. -/
theorem run_stack_length_le (r : LengthControlledOracleReduction ea eb ec ed f g)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle ec ed g oracle)
    (a : α) (t : ℕ) (c : r.reduction.machine.Cfg)
    (ht : t ≤ r.reduction.time.eval (ea.encode a).length)
    (hr : r.reduction.machine.run oracle (ea.encode a) t = some c)
    (k : r.reduction.machine.K) :
    (c.stk k).length ≤ r.sourceOutputPolynomial.eval (ea.encode a).length := by
  have hs := r.run_stackSize_le oracle ho a t c hr
  have hk := stack_length_le_stackSize c.stk k
  have hm := Nat.mul_le_mul_right (r.reduction.machine.primitiveBudget +
    (r.targetOutput.bound.comp r.queryBound).eval (ea.encode a).length) ht
  simp only [sourceOutputPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

/-- One compiled caller transition has this uniform polynomial cost. The terms
pay for the callee, copying the query, clearing the old answer, and returning the
new answer, with the explicit fixed overhead of the finite protocol. -/
noncomputable def compositionMacroPolynomial
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : PolyTimeOracleReduction ec ed ee ef g h) : Polynomial ℕ :=
  r₂.time.comp r₁.queryBound + 2 * r₁.queryBound + r₁.sourceOutputPolynomial +
    3 * (r₁.targetOutput.bound.comp r₁.queryBound) + 9

theorem compositionMacroPolynomial_pos
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : PolyTimeOracleReduction ec ed ee ef g h) (n : ℕ) :
    1 ≤ (r₁.compositionMacroPolynomial r₂).eval n := by
  simp only [compositionMacroPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat]
  omega

/-- All size-dependent costs of one actual query are controlled by the original
input length. This bound uses no query or output annotation for the callee. -/
theorem composition_cost_le
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : PolyTimeOracleReduction ec ed ee ef g h)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle ec ed g oracle)
    (a : α) (t : ℕ) (c : r₁.reduction.machine.Cfg)
    (ht : t ≤ r₁.reduction.time.eval (ea.encode a).length)
    (hr : r₁.reduction.machine.run oracle (ea.encode a) t = some c)
    (hq : r₁.reduction.machine.IsQuery c) :
    r₂.time.eval (c.stk r₁.reduction.machine.queryStack).length +
      2 * (c.stk r₁.reduction.machine.queryStack).length +
      (c.stk r₁.reduction.machine.answerStack).length +
      3 * (oracle (c.stk r₁.reduction.machine.queryStack)).length + 9 ≤
        (r₁.compositionMacroPolynomial r₂).eval (ea.encode a).length := by
  obtain ⟨q, he, hlen⟩ := r₁.safeQuery oracle ho a t c hr hq
  have htime := natPolynomial_eval_mono r₂.time hlen
  have hstack := r₁.run_stack_length_le oracle ho a t c ht hr
    r₁.reduction.machine.answerStack
  have hanswer := r₁.answer_length_le oracle ho a t c hr hq
  simp only [compositionMacroPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_comp]
  simp only [Polynomial.eval_comp] at hanswer
  omega

/-- The full polynomial multiplies the caller's transition budget by its
uniform actual compiled transition budget. -/
noncomputable def compositionTimePolynomial
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : PolyTimeOracleReduction ec ed ee ef g h) : Polynomial ℕ :=
  r₁.reduction.time * r₁.compositionMacroPolynomial r₂

/-- Every reachable, valid caller query has an actual callee computation with
all copying and clearing costs bounded by the one uniform polynomial. -/
noncomputable def compositionCallBound
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : PolyTimeOracleReduction ec ed ee ef g h)
    (outer inner : List Bool → List Bool)
    (ho : RepresentsOracle ec ed g outer) (hi : RepresentsOracle ee ef h inner)
    (a : α) (t : ℕ) (c : r₁.reduction.machine.Cfg)
    (ht : t ≤ r₁.reduction.time.eval (ea.encode a).length)
    (hr : r₁.reduction.machine.run outer (ea.encode a) t = some c)
    (hq : r₁.reduction.machine.IsQuery c) :
    OracleCompose.CallBound r₂.machine r₁.reduction.machine inner outer c
      ((r₁.compositionMacroPolynomial r₂).eval (ea.encode a).length) := by
  classical
  let q := Classical.choose (r₁.safeQuery outer ho a t c hr hq)
  have he := (Classical.choose_spec (r₁.safeQuery outer ho a t c hr hq)).1
  refine ⟨r₂.time.eval (c.stk r₁.reduction.machine.queryStack).length, ?_,
    r₁.composition_cost_le r₂ outer ho a t c ht hr hq⟩
  rw [he, ho]
  exact r₂.correct inner hi q

/-- Transitivity through a length-controlled first reduction is realized by
the finite caller compiler, with a proved polynomial bound on actual steps.
It works for every valid extension of the final oracle on malformed strings. -/
noncomputable def compose
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : PolyTimeOracleReduction ec ed ee ef g h) :
    PolyTimeOracleReduction ea eb ee ef f h where
  machine := OracleCompose.machine r₂.machine r₁.reduction.machine
  time := r₁.compositionTimePolynomial r₂
  correct oracle ho a := by
    have houter := encodedOracle_represents ec ed g
    have run := OracleCompose.outputs r₂.machine r₁.reduction.machine
      (encodedOracle ec ed g) oracle (ea.encode a) (eb.encode (f a))
      (r₁.reduction.time.eval (ea.encode a).length)
      ((r₁.compositionMacroPolynomial r₂).eval (ea.encode a).length)
      (r₁.reduction.correct (encodedOracle ec ed g) houter a)
      (r₁.compositionMacroPolynomial_pos r₂ _)
      (fun t c ht hr hq => r₁.compositionCallBound r₂ (encodedOracle ec ed g) oracle
        houter ho a t c (Nat.le_of_lt ht) hr hq)
    simpa only [compositionTimePolynomial, Polynomial.eval_mul] using run

/-- Existential form of the proved encoded composition theorem, retaining its
necessary first-stage validity and word-length hypotheses. -/
theorem oracleReducible_comp
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : OracleReducible ec ed ee ef g h) : OracleReducible ea eb ee ef f h := by
  obtain ⟨r₂⟩ := r₂
  exact ⟨r₁.compose r₂⟩

end LengthControlledOracleReduction
end Holant.Complexity
