import Holant.Complexity.OracleOneQuery.ContextProgram

/-! Polynomial-time one-query reductions with an actual retained context word.
This is the interface for input-dependent scalar correction after a fixed-gadget
oracle call. The query compiler and correction program must both be proved
finite-machine computations; no such domain-specific compiler is assumed here. -/
namespace Holant.Complexity.OracleOneQuery.Context
open Computability BinaryCompose FixedFieldMachines Holant.Algebraic

variable {α β γ δ ε : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool} {ee : Encoding ε Bool}
  {pre : α → γ × ε} {post : δ × ε → β} {g : γ → δ}

noncomputable def answerBound (a : Computes ea (pairEncoding ec ee) pre)
    (size : PolynomialOutputBound ec ed g) : Polynomial ℕ :=
  size.bound.comp a.outputBound.bound

noncomputable def decoderBound (a : Computes ea (pairEncoding ec ee) pre)
    (size : PolynomialOutputBound ec ed g) : Polynomial ℕ :=
  2 * answerBound a size + 1 + a.outputBound.bound

theorem query_context_length_le (a : Computes ea (pairEncoding ec ee) pre) (x : α) :
    (ec.encode (pre x).1).length ≤ a.outputBound.bound.eval (ea.encode x).length ∧
    (ee.encode (pre x).2).length ≤ a.outputBound.bound.eval (ea.encode x).length := by
  have h := a.outputBound.length_le x
  rw [pairEncoding_length] at h
  constructor <;> omega

theorem answer_length_le (a : Computes ea (pairEncoding ec ee) pre)
    (size : PolynomialOutputBound ec ed g) (x : α) :
    (ed.encode (g (pre x).1)).length ≤ (answerBound a size).eval (ea.encode x).length := by
  exact le_trans (size.length_le (pre x).1)
    (by simpa [answerBound] using
      natPolynomial_eval_mono size.bound (query_context_length_le a x).1)

theorem decoder_length_le (a : Computes ea (pairEncoding ec ee) pre)
    (size : PolynomialOutputBound ec ed g) (x : α) :
    ((pairEncoding ed ee).encode (g (pre x).1, (pre x).2)).length ≤
      (decoderBound a size).eval (ea.encode x).length := by
  have ha := answer_length_le a size x
  have hc := (query_context_length_le a x).2
  simp only [pairEncoding_length, decoderBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

/-- The sole query excludes the caller context; the decoder receives both actual
answer and retained context, with an explicit original-input polynomial bound. -/
noncomputable def reduction (a : Computes ea (pairEncoding ec ee) pre)
    (b : Computes (pairEncoding ed ee) eb post) (size : PolynomialOutputBound ec ed g) :
    PolyTimeOracleReduction ea eb ec ed (fun x => post (g (pre x).1, (pre x).2)) g where
  machine := machine a.machine b.machine
  time := a.time + (2 * a.outputBound.bound + 2 * answerBound a size + 6) +
    2 * (decoderBound a size + 1) + b.time.comp (decoderBound a size)
  correct oracle ho x := by
    have hb : Turing.TM2OutputsInTime b.machine.computer
        (frame (oracle (ec.encode (pre x).1)) ++ ee.encode (pre x).2)
        (some (eb.encode (post (g (pre x).1, (pre x).2))))
        (b.time.eval ((pairEncoding ed ee).encode (g (pre x).1, (pre x).2)).length) := by
      rw [ho (pre x).1]
      exact b.outputs (g (pre x).1, (pre x).2)
    have h := outputs a.machine b.machine oracle (ea.encode x) (ec.encode (pre x).1)
      (ee.encode (pre x).2) (eb.encode (post (g (pre x).1, (pre x).2)))
      (a.time.eval (ea.encode x).length)
      (b.time.eval ((pairEncoding ed ee).encode (g (pre x).1, (pre x).2)).length)
      (a.outputs x) hb
    refine { steps := h.steps, evals_in_steps := h.evals_in_steps, steps_le_m := ?_ }
    apply le_trans h.steps_le_m
    have hq := (query_context_length_le a x).1
    have ha := answer_length_le a size x
    have hd := decoder_length_le a size x
    have ht := natPolynomial_eval_mono b.time hd
    rw [ho (pre x).1]
    change (frame (ed.encode (g (pre x).1)) ++ ee.encode (pre x).2).length ≤ _ at hd
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one, Polynomial.eval_comp]
    omega

noncomputable def of_eq (a : Computes ea (pairEncoding ec ee) pre)
    (b : Computes (pairEncoding ed ee) eb post) (size : PolynomialOutputBound ec ed g)
    (f : α → β) (heq : ∀ x, f x = post (g (pre x).1, (pre x).2)) :
    PolyTimeOracleReduction ea eb ec ed f g := by
  have hf : f = fun x => post (g (pre x).1, (pre x).2) := funext heq
  subst f
  exact reduction a b size

theorem reducible (a : Computes ea (pairEncoding ec ee) pre)
    (b : Computes (pairEncoding ed ee) eb post) (size : PolynomialOutputBound ec ed g)
    (f : α → β) (heq : ∀ x, f x = post (g (pre x).1, (pre x).2)) :
    OracleReducible ea eb ec ed f g := ⟨of_eq a b size f heq⟩

end Holant.Complexity.OracleOneQuery.Context
