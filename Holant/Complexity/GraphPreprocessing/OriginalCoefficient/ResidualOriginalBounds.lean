import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalCoefficient

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalCoefficient
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

noncomputable def parentPrimitivePolynomial (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  parentTimePolynomial a z s b arity*Polynomial.C (parentMachine a z s b arity).primitiveBudget
theorem parent_primitive_bound (a z : Bool) (x : ResidualContext.Query s b arity) :
    primitiveCost (parentMachine a z s b arity) (parent_timed a z x).steps
      (some (initList (parentMachine a z s b arity).computer ((ResidualContext.queryEncoding s b arity).encode x))) ≤
      (parentPrimitivePolynomial a z s b arity).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length := by
  have h := Nat.mul_le_mul_right (parentMachine a z s b arity).primitiveBudget (parent_timed a z x).steps_le_m
  simpa only [parentPrimitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

noncomputable def zeroTimePolynomial (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (zeroComputes a z s b arity).time.comp (7*(Polynomial.X+1))
noncomputable def zero_timed (a z : Bool) (x : ResidualContext.Query s b arity) :
    TM2OutputsInTime (zeroMachine a z s b arity).computer ((ResidualContext.queryEncoding s b arity).encode x)
      (some ((treeLabelEncoding s b arity).encode (zeroValue a z x)))
      ((zeroTimePolynomial a z s b arity).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length) where
  steps := ((zeroComputes a z s b arity).outputs x).steps
  evals_in_steps := ((zeroComputes a z s b arity).outputs x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (zeroComputes a z s b arity).time (ResidualContext.query_length x)
    exact le_trans ((zeroComputes a z s b arity).outputs x).steps_le_m (by simpa [zeroTimePolynomial] using h)
noncomputable def zeroPrimitivePolynomial (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  zeroTimePolynomial a z s b arity*Polynomial.C (zeroMachine a z s b arity).primitiveBudget
theorem zero_primitive_bound (a z : Bool) (x : ResidualContext.Query s b arity) :
    primitiveCost (zeroMachine a z s b arity) (zero_timed a z x).steps
      (some (initList (zeroMachine a z s b arity).computer ((ResidualContext.queryEncoding s b arity).encode x))) ≤
      (zeroPrimitivePolynomial a z s b arity).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length := by
  have h := Nat.mul_le_mul_right (zeroMachine a z s b arity).primitiveBudget (zero_timed a z x).steps_le_m
  simpa only [zeroPrimitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
theorem parent_output_length (a z : Bool) (x : ResidualContext.Query s b arity) :
    ((treeLabelEncoding s b arity).encode (parentValue a z x)).length≤lengthBound s b arity :=
  treeLabelEncoding_length_le s b arity _
theorem zero_output_length (a z : Bool) (x : ResidualContext.Query s b arity) :
    ((treeLabelEncoding s b arity).encode (zeroValue a z x)).length≤lengthBound s b arity :=
  treeLabelEncoding_length_le s b arity _
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalCoefficient
