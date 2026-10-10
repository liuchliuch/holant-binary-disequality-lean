import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

theorem input_length_le (x : Input s b arity) :
    ((inputEncoding s b arity).encode x).length≤7*((RawClosedNetwork.encoding.encode x.1.1.val).length+1) := by
  have hi := RawRootReach.input_length_le_original x.1
  have hc := x.1.1.val.counts_le_encoded_length
  have hv := x.2.isLt
  change (Holant.Algebraic.frame ((RawRootReach.inputEncoding s b arity).encode x.1)++List.replicate x.2.val true).length≤_
  simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega
theorem output_length (x : Input s b arity) :
    (value x).length≤4*lengthBound s b arity+x.2.val+6 := by
  have h := treeLabelEncoding_length_le s b arity (ParentCoefficient.value true (prepared x))
  simp only [value,portAction,List.length_append,Traversal.literals_length,List.length_cons,
    Holant.Algebraic.frame_length,Traversal.reference_length]
  omega
noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (computes s b arity).time.comp (7*(Polynomial.X+1))
noncomputable def timed (x : Input s b arity) :
    TM2OutputsInTime (machine s b arity).computer ((inputEncoding s b arity).encode x)
      (some (value x)) ((timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.1.val).length) where
  steps := ((computes s b arity).outputs x).steps
  evals_in_steps := ((computes s b arity).outputs x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (computes s b arity).time (input_length_le x)
    exact le_trans ((computes s b arity).outputs x).steps_le_m (by simpa [timePolynomial] using h)
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial s b arity*Polynomial.C (machine s b arity).primitiveBudget
theorem primitive_bound (x : Input s b arity) :
    primitiveCost (machine s b arity) (timed x).steps
      (some (initList (machine s b arity).computer ((inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.1.val).length := by
  have h := Nat.mul_le_mul_right (machine s b arity).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild
