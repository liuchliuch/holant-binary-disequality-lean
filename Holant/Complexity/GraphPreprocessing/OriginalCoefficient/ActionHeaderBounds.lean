import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeader

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeader
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

theorem emit_length (x : Data s b arity) : (emit s b arity x).length≤8*lengthBound s b arity+4 := by
  have ha := treeLabelEncoding_length_le s b arity x.2.1
  have hb := treeLabelEncoding_length_le s b arity x.2.2
  unfold emit
  rw [Traversal.literals_length,List.length_append]
  cases h : x.1 <;> simp only [h,Bool.false_eq_true,↓reduceIte,Holant.Algebraic.frame_length,List.length_nil] <;> omega
theorem output_length (x : ParentCoefficient.Input s b arity) : (value x).length≤8*lengthBound s b arity+4 := emit_length _
noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes s b arity).time
noncomputable def timed (x : ParentCoefficient.Input s b arity) :
    TM2OutputsInTime (machine s b arity).computer ((ParentCoefficient.inputEncoding s b arity).encode x)
      (some (value x)) ((timePolynomial s b arity).eval ((ParentCoefficient.inputEncoding s b arity).encode x).length) :=
  (computes s b arity).outputs x
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial s b arity*Polynomial.C (machine s b arity).primitiveBudget
theorem primitive_bound (x : ParentCoefficient.Input s b arity) :
    primitiveCost (machine s b arity) (timed x).steps
      (some (initList (machine s b arity).computer ((ParentCoefficient.inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity).eval ((ParentCoefficient.inputEncoding s b arity).encode x).length := by
  have h := Nat.mul_le_mul_right (machine s b arity).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeader
