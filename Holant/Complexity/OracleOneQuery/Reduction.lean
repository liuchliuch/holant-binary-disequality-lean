import Holant.Complexity.OracleOneQuery.Program

/-!
# A proved one-query reduction from explicit input and answer programs

The oracle answer-size bound is an explicit mathematical requirement. It cannot
be replaced by unit-cost processing of arbitrarily long oracle answers. The
input compiler's output bound, in contrast, follows from its actual transitions.
This module does not by itself construct a fixed-gadget compiler or the
input-dependent scalar correction required by projective gadget substitution.
-/

namespace Holant.Complexity.OracleOneQuery
open Computability BinaryCompose

variable {α β γ δ : Type}
    {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool}
    {pre : α → γ} {post : δ → β} {g : γ → δ}

/-- The size of an actual oracle answer is bounded in terms of the original input. -/
noncomputable def answerBound (a : Computes ea ec pre)
    (size : PolynomialOutputBound ec ed g) : Polynomial ℕ :=
  size.bound.comp a.outputBound.bound

theorem answer_length_le (a : Computes ea ec pre)
    (size : PolynomialOutputBound ec ed g) (x : α) :
    (ed.encode (g (pre x))).length ≤ (answerBound a size).eval (ea.encode x).length := by
  exact le_trans (size.length_le (pre x))
    (by simpa [answerBound] using
      natPolynomial_eval_mono size.bound (a.outputBound.length_le x))

/-- A fixed finite oracle program, with every answer-copying step charged. -/
noncomputable def reduction (a : Computes ea ec pre) (b : Computes ed eb post)
    (size : PolynomialOutputBound ec ed g) :
    PolyTimeOracleReduction ea eb ec ed (post ∘ g ∘ pre) g where
  machine := machine a.machine b.machine
  time := a.time + 1 + 2 * (answerBound a size + 1) + b.time.comp (answerBound a size)
  correct oracle ho x := by
    have hb : Turing.TM2OutputsInTime b.machine.computer (oracle (ec.encode (pre x)))
        (some (eb.encode (post (g (pre x)))))
        (b.time.eval (ed.encode (g (pre x))).length) := by
      rw [ho (pre x)]
      exact b.outputs (g (pre x))
    have h := outputs a.machine b.machine oracle (ea.encode x) (ec.encode (pre x))
      (eb.encode (post (g (pre x)))) (a.time.eval (ea.encode x).length)
      (b.time.eval (ed.encode (g (pre x))).length) (a.outputs x) hb
    refine { steps := h.steps, evals_in_steps := h.evals_in_steps, steps_le_m := ?_ }
    apply le_trans h.steps_le_m
    have hs := answer_length_le a size x
    have ht := natPolynomial_eval_mono b.time hs
    rw [ho (pre x)]
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_comp]
    omega

/-- The semantic identity is checked separately from the implemented reduction. -/
noncomputable def of_eq (a : Computes ea ec pre) (b : Computes ed eb post)
    (size : PolynomialOutputBound ec ed g) (f : α → β)
    (heq : ∀ x, f x = post (g (pre x))) : PolyTimeOracleReduction ea eb ec ed f g := by
  have hfun : f = post ∘ g ∘ pre := funext heq
  subst f
  exact reduction a b size

theorem reducible (a : Computes ea ec pre) (b : Computes ed eb post)
    (size : PolynomialOutputBound ec ed g) (f : α → β)
    (heq : ∀ x, f x = post (g (pre x))) : OracleReducible ea eb ec ed f g :=
  ⟨of_eq a b size f heq⟩

end Holant.Complexity.OracleOneQuery
