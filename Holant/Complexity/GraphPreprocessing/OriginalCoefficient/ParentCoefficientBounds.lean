import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficient

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficient
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

noncomputable def timePolynomial (flip : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes flip s b arity).time
noncomputable def timed (flip : Bool) (x : Input s b arity) :
    TM2OutputsInTime (machine flip s b arity).computer ((inputEncoding s b arity).encode x)
      (some ((treeLabelEncoding s b arity).encode (value flip x)))
      ((timePolynomial flip s b arity).eval ((inputEncoding s b arity).encode x).length) := (computes flip s b arity).outputs x
noncomputable def primitivePolynomial (flip : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial flip s b arity*Polynomial.C (machine flip s b arity).primitiveBudget
theorem primitive_bound (flip : Bool) (x : Input s b arity) :
    primitiveCost (machine flip s b arity) (timed flip x).steps
      (some (initList (machine flip s b arity).computer ((inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial flip s b arity).eval ((inputEncoding s b arity).encode x).length := by
  have h := Nat.mul_le_mul_right (machine flip s b arity).primitiveBudget (timed flip x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

abbrev originalMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine identityMachine RawParentRow.machine).compose (machine false s b arity)
@[simp] theorem original_machine (s b : ℕ) (arity : ℕ → ℕ) :
    (originalComputes s b arity).machine=originalMachine s b arity := rfl
theorem original_inFP : InFP (RawRootReach.inputEncoding s b arity) (treeLabelEncoding s b arity)
    (fun x => value false (originalInput x)) := (originalComputes s b arity).inFP
noncomputable def originalTimePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (originalComputes s b arity).time.comp (3*(Polynomial.X+1))
noncomputable def original_timed (x : RawRootReach.Input s b arity) :
    TM2OutputsInTime (originalMachine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x)
      (some ((treeLabelEncoding s b arity).encode (value false (originalInput x))))
      ((originalTimePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := ((originalComputes s b arity).outputs x).steps
  evals_in_steps := ((originalComputes s b arity).outputs x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (originalComputes s b arity).time (RawRootReach.input_length_le_original x)
    exact le_trans ((originalComputes s b arity).outputs x).steps_le_m (by simpa [originalTimePolynomial] using h)

noncomputable def originalPrimitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  originalTimePolynomial s b arity*Polynomial.C (originalMachine s b arity).primitiveBudget
theorem original_primitive_bound (x : RawRootReach.Input s b arity) :
    primitiveCost (originalMachine s b arity) (original_timed x).steps
      (some (initList (originalMachine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x))) ≤
      (originalPrimitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  have h := Nat.mul_le_mul_right (originalMachine s b arity).primitiveBudget (original_timed x).steps_le_m
  simpa only [originalPrimitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficient
