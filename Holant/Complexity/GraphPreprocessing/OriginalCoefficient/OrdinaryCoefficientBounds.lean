import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficient

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficient
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes s b arity).time
noncomputable def timed (x : Input s b arity) :
    TM2OutputsInTime (machine s b arity).computer ((inputEncoding s b arity).encode x)
      (some ((treeLabelEncoding s b arity).encode (value x)))
      ((timePolynomial s b arity).eval ((inputEncoding s b arity).encode x).length) := (computes s b arity).outputs x
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial s b arity*Polynomial.C (machine s b arity).primitiveBudget
theorem primitive_bound (x : Input s b arity) :
    primitiveCost (machine s b arity) (timed x).steps
      (some (initList (machine s b arity).computer ((inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity).eval ((inputEncoding s b arity).encode x).length := by
  have h := Nat.mul_le_mul_right (machine s b arity).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

noncomputable def zeroTimePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (zeroComputes s b arity).time.comp (3*(Polynomial.X+1))
noncomputable def zero_timed_original (x : RawRootReach.Input s b arity) :
    TM2OutputsInTime (zeroMachine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x)
      (some ((treeLabelEncoding s b arity).encode (zeroValue x)))
      ((zeroTimePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := ((zeroComputes s b arity).outputs x).steps
  evals_in_steps := ((zeroComputes s b arity).outputs x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (zeroComputes s b arity).time (RawRootReach.input_length_le_original x)
    exact le_trans ((zeroComputes s b arity).outputs x).steps_le_m (by simpa [zeroTimePolynomial] using h)
theorem output_length (x : Input s b arity) :
    ((treeLabelEncoding s b arity).encode (value x)).length ≤ lengthBound s b arity :=
  treeLabelEncoding_length_le s b arity _
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficient
