import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWord
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWord
open Turing Computability BinaryCompose FixedFieldMachines
variable {s b : ℕ} {arity : ℕ → ℕ}

theorem input_length_le_original (x : Input s b arity) :
    ((inputEncoding s b arity).encode x).length ≤ 3*((RawClosedNetwork.encoding.encode x.1.val).length+1) := by
  have hn := x.1.val.counts_le_encoded_length
  have he := x.2.isLt
  change (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode x.1.val) ++ List.replicate x.2.val true).length ≤ _
  simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

noncomputable def originalTimePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (timePolynomial s b arity).comp (3*(Polynomial.X+1))

noncomputable def timed_original (x : Input s b arity) :
    TM2OutputsInTime machine.computer ((inputEncoding s b arity).encode x) (some (word x))
      ((originalTimePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := (timed x).steps
  evals_in_steps := (timed x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (timePolynomial s b arity) (input_length_le_original x)
    exact le_trans (timed x).steps_le_m (by simpa [originalTimePolynomial] using h)

noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  originalTimePolynomial s b arity * Polynomial.C machine.primitiveBudget

theorem primitive_bound (x : Input s b arity) :
    primitiveCost machine (timed_original x).steps
      (some (initList machine.computer ((inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed_original x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    le_trans (primitiveCost_le _ _ _) h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWord
