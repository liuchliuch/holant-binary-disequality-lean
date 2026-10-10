import Holant.Complexity.OracleInline
import Holant.Complexity.OracleQueryBounds

/-! # Polynomial accounting for an actual inlined oracle call -/

namespace Holant.Complexity.OracleInline

open Turing

/-- The bound includes the previous answer, which really is erased bit by bit. -/
noncomputable def callPolynomial (time query oldAnswer newAnswer : Polynomial ℕ) : Polynomial ℕ :=
  time.comp query + 2 * query + oldAnswer + 3 * newAnswer + 8

variable {J R τ : Type} [DecidableEq J] [Fintype J] [Fintype R] [Fintype τ]

/-- Polynomial word bounds yield a polynomial for the proved operational call,
without treating copying, replacement, or cleanup as unit-cost. -/
def call_polynomial (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (memory : τ) (frame : J → List Bool) (value : List Bool)
    (time queryBound oldAnswer newAnswer : Polynomial ℕ) (n : ℕ)
    (hq : (frame query).length ≤ queryBound.eval n)
    (ha : (frame answer).length ≤ oldAnswer.eval n)
    (hv : value.length ≤ newAnswer.eval n)
    (h : m.OutputsInTime oracle (frame query) value (time.eval (frame query).length)) :
    StateTransition.EvalsToInTime ((machine m query answer initialMemory ret outside).step oracle)
      (cfg m (phase m R 0) memory (fun _ => []) frame)
      (some (cfg m (.inr (.inr (ret memory))) memory (fun _ => []) (Function.update frame answer value)))
      ((callPolynomial time queryBound oldAnswer newAnswer).eval n) := by
  let run := call_correct m query answer initialMemory ret outside oracle memory frame value _ h
  refine ⟨run.toEvalsTo, le_trans run.steps_le_m ?_⟩
  have ht := natPolynomial_eval_mono time hq
  simp only [callPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_ofNat]
  omega

end Holant.Complexity.OracleInline
