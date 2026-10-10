import Holant.Complexity.OracleBatch.EncodingBounds

namespace Holant.Complexity.OracleBatch
open Computability BinaryCompose FixedFieldMachines Holant.Algebraic
variable {α β γ δ ε : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {eq : Encoding γ Bool} {ed : Encoding δ Bool} {ee : Encoding ε Bool}
  {pre : α → List γ × ε} {post : List δ × ε → β} {g : γ → δ}

/-- Derive one actual polynomial-time oracle machine from two actual ordinary
programs and the target's output-length bound. No desired reduction is supplied. -/
noncomputable def reduction (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g) :
    PolyTimeOracleReduction ea eb eq ed (fun x => post (answers g (pre x))) g where
  machine := machine a.machine b.machine
  time := a.time + 16 * (a.outputBound.bound + decoderBound a size + 1) +
    b.time.comp (decoderBound a size)
  correct oracle ho x := by
    have hm := oracle_encoded_list oracle ho (pre x).1
    have ha : Turing.TM2OutputsInTime a.machine.computer (ea.encode x)
        (some (word ((pre x).1.map eq.encode) (ee.encode (pre x).2)))
        (a.time.eval (ea.encode x).length) := by
      simpa only [context_encode] using a.outputs x
    have hb : Turing.TM2OutputsInTime b.machine.computer
        (word (((pre x).1.map eq.encode).map oracle) (ee.encode (pre x).2))
        (some (eb.encode (post (answers g (pre x)))))
        (b.time.eval ((contextEncoding ed ee).encode (answers g (pre x))).length) := by
      simpa only [context_encode,answers,hm] using b.outputs (answers g (pre x))
    have h := outputs a.machine b.machine oracle (ea.encode x) ((pre x).1.map eq.encode)
      (ee.encode (pre x).2) (eb.encode (post (answers g (pre x))))
      (a.time.eval (ea.encode x).length)
      (b.time.eval ((contextEncoding ed ee).encode (answers g (pre x))).length) ha hb
    refine { steps := h.steps, evals_in_steps := h.evals_in_steps, steps_le_m := ?_ }
    apply le_trans h.steps_le_m
    have hp := a.outputBound.length_le x
    have hd := decoder_length_le a size x
    have ht := natPolynomial_eval_mono b.time hd
    have hc := overhead_le oracle ((pre x).1.map eq.encode) (ee.encode (pre x).2)
    rw [context_encode] at hp
    simp only [context_encode,answers] at hd
    rw [hm] at hc
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_one,Polynomial.eval_comp]
    omega

noncomputable def of_eq (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g)
    (f : α → β) (heq : ∀ x, f x = post (answers g (pre x))) :
    PolyTimeOracleReduction ea eb eq ed f g where
  machine := (reduction a b size).machine
  time := (reduction a b size).time
  correct oracle ho x := by simpa only [heq x] using (reduction a b size).correct oracle ho x

end Holant.Complexity.OracleBatch
