import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanEncoding

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

/-- The chosen number is only a proof witness extracted from the complete
operational induction. The finite program contains no choice or size oracle. -/
noncomputable def timed (x : Input) :
    TM2OutputsInTime (machine actual).computer (inputEncoding.encode x)
      (some (ParentRowEncoding.parent.encode (value x)))
      (timePolynomial.eval (inputEncoding.encode x).length) where
  steps := Classical.choose (whole_run x.1 x.2.1 x.2.2)
  evals_in_steps := (Classical.choose_spec (whole_run x.1 x.2.1 x.2.2)).2
  steps_le_m := (Classical.choose_spec (whole_run x.1 x.2.1 x.2.2)).1

noncomputable def computes : Computes inputEncoding ParentRowEncoding.parent value where
  machine := machine actual
  time := timePolynomial
  outputs := timed

theorem inFP : InFP inputEncoding ParentRowEncoding.parent value := computes.inFP

noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial*Polynomial.C (machine actual).primitiveBudget

theorem primitive_bound (x : Input) :
    primitiveCost (machine actual) (timed x).steps (some (initList (machine actual).computer (inputEncoding.encode x))) ≤
      primitivePolynomial.eval (inputEncoding.encode x).length := by
  have h := Nat.mul_le_mul_right (machine actual).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    le_trans (primitiveCost_le _ _ _) h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
