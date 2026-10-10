import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ThreeQueryProgram
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ThreeQueryBound
import Holant.Complexity.OracleOneQuery.ContextReduction

/-! A polynomial-time three-query caller from concrete ordinary compiler and
decoder programs. All three actual answer lengths are charged using the supplied
target function's polynomial output bound. -/
namespace Holant.Complexity.UniversalPairReduction.ThreeQuery
open Computability BinaryCompose FixedFieldMachines Holant.Algebraic

/-- Literal right-associated framing of three words followed by caller context. -/
def contextEncoding {γ ε : Type} (eq : Encoding γ Bool) (ee : Encoding ε Bool) :=
  pairEncoding eq (pairEncoding eq (pairEncoding eq ee))

@[simp] theorem contextEncoding_length {γ ε : Type}
    (eq : Encoding γ Bool) (ee : Encoding ε Bool) (v : γ × (γ × (γ × ε))) :
    ((contextEncoding eq ee).encode v).length =
      2 * ((eq.encode v.1).length + (eq.encode v.2.1).length + (eq.encode v.2.2.1).length) +
        3 + (ee.encode v.2.2.2).length := by
  simp only [contextEncoding,pairEncoding_length]
  omega

variable {α β γ δ ε : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {eq : Encoding γ Bool} {ed : Encoding δ Bool} {ee : Encoding ε Bool}
  {pre : α → γ × (γ × (γ × ε))} {post : δ × (δ × (δ × ε)) → β} {g : γ → δ}

/-- The values of three actual target calls, in the original query order. -/
def answers (g : γ → δ) (v : γ × (γ × (γ × ε))) : δ × (δ × (δ × ε)) :=
  (g v.1,(g v.2.1,(g v.2.2.1,v.2.2.2)))

noncomputable def answerBound (a : Computes ea (contextEncoding eq ee) pre)
    (size : PolynomialOutputBound eq ed g) : Polynomial ℕ :=
  size.bound.comp a.outputBound.bound
noncomputable def decoderBound (a : Computes ea (contextEncoding eq ee) pre)
    (size : PolynomialOutputBound eq ed g) : Polynomial ℕ :=
  6 * answerBound a size + 3 + a.outputBound.bound

theorem query_context_length_le (a : Computes ea (contextEncoding eq ee) pre) (x : α) :
    (eq.encode (pre x).1).length ≤ a.outputBound.bound.eval (ea.encode x).length ∧
    (eq.encode (pre x).2.1).length ≤ a.outputBound.bound.eval (ea.encode x).length ∧
    (eq.encode (pre x).2.2.1).length ≤ a.outputBound.bound.eval (ea.encode x).length ∧
    (ee.encode (pre x).2.2.2).length ≤ a.outputBound.bound.eval (ea.encode x).length := by
  have h := a.outputBound.length_le x
  rw [contextEncoding_length] at h
  omega

theorem answer_length_le (a : Computes ea (contextEncoding eq ee) pre)
    (size : PolynomialOutputBound eq ed g) (x : α) :
    (ed.encode (g (pre x).1)).length ≤ (answerBound a size).eval (ea.encode x).length ∧
    (ed.encode (g (pre x).2.1)).length ≤ (answerBound a size).eval (ea.encode x).length ∧
    (ed.encode (g (pre x).2.2.1)).length ≤ (answerBound a size).eval (ea.encode x).length := by
  have h := query_context_length_le a x
  refine ⟨?_,?_,?_⟩
  · exact le_trans (size.length_le (pre x).1)
      (by simpa [answerBound] using natPolynomial_eval_mono size.bound h.1)
  · exact le_trans (size.length_le (pre x).2.1)
      (by simpa [answerBound] using natPolynomial_eval_mono size.bound h.2.1)
  · exact le_trans (size.length_le (pre x).2.2.1)
      (by simpa [answerBound] using natPolynomial_eval_mono size.bound h.2.2.1)

theorem decoder_length_le (a : Computes ea (contextEncoding eq ee) pre)
    (size : PolynomialOutputBound eq ed g) (x : α) :
    ((contextEncoding ed ee).encode (answers g (pre x))).length ≤
      (decoderBound a size).eval (ea.encode x).length := by
  have ha := answer_length_le a size x
  have hc := (query_context_length_le a x).2.2.2
  simp only [contextEncoding_length,answers,decoderBound,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega

/-- No oracle reduction is supplied: the witness is the explicit finite caller
with three query transitions and the two given ordinary finite machines. -/
noncomputable def reduction (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g) :
    PolyTimeOracleReduction ea eb eq ed (fun x => post (answers g (pre x))) g where
  machine := machine a.machine b.machine
  time := a.time + (6 * a.outputBound.bound + 6 * answerBound a size + 18) +
    2 * (decoderBound a size + 1) + b.time.comp (decoderBound a size)
  correct oracle ho x := by
    have hb : Turing.TM2OutputsInTime b.machine.computer
        (word (oracle (eq.encode (pre x).1)) (oracle (eq.encode (pre x).2.1))
          (oracle (eq.encode (pre x).2.2.1)) (ee.encode (pre x).2.2.2))
        (some (eb.encode (post (answers g (pre x)))))
        (b.time.eval ((contextEncoding ed ee).encode (answers g (pre x))).length) := by
      rw [ho (pre x).1,ho (pre x).2.1,ho (pre x).2.2.1]
      exact b.outputs (answers g (pre x))
    have h := outputs a.machine b.machine oracle (ea.encode x)
      (eq.encode (pre x).1) (eq.encode (pre x).2.1) (eq.encode (pre x).2.2.1)
      (ee.encode (pre x).2.2.2) (eb.encode (post (answers g (pre x))))
      (a.time.eval (ea.encode x).length)
      (b.time.eval ((contextEncoding ed ee).encode (answers g (pre x))).length)
      (a.outputs x) hb
    refine { steps := h.steps, evals_in_steps := h.evals_in_steps, steps_le_m := ?_ }
    apply le_trans h.steps_le_m
    have hq := query_context_length_le a x
    have ha := answer_length_le a size x
    have hd := decoder_length_le a size x
    have ht := natPolynomial_eval_mono b.time hd
    rw [ho (pre x).1,ho (pre x).2.1,ho (pre x).2.2.1]
    change (word (ed.encode (g (pre x).1)) (ed.encode (g (pre x).2.1))
      (ed.encode (g (pre x).2.2.1)) (ee.encode (pre x).2.2.2)).length ≤ _ at hd
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_one,Polynomial.eval_comp]
    omega

noncomputable def of_eq (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g)
    (f : α → β) (heq : ∀ x, f x = post (answers g (pre x))) :
    PolyTimeOracleReduction ea eb eq ed f g where
  machine := (reduction a b size).machine
  time := (reduction a b size).time
  correct oracle ho x := by
    simpa only [heq x] using (reduction a b size).correct oracle ho x

/-- The end-to-end reduction has a genuine three-query bound on all prefixes. -/
theorem reduction_atMostThree (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g) :
    AtMostQueries (reduction a b size).machine 3 := atMostThree a.machine b.machine

theorem of_eq_atMostThree (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g)
    (f : α → β) (heq : ∀ x, f x = post (answers g (pre x))) :
    AtMostQueries (of_eq a b size f heq).machine 3 := atMostThree a.machine b.machine

end Holant.Complexity.UniversalPairReduction.ThreeQuery
