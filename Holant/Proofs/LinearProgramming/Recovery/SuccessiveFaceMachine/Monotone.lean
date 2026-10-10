import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.Source
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Source

set_option autoImplicit false

/-! Kernel-checked recovery component. Appending a physically emitted fixation row cannot
shrink the original word. Hence the old current-face isolation grid is at
least as fine as the grid required by the ORIGINAL denominator bound.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines Codec
namespace Monotone
theorem append_word {A : Type} (e : Encoding A Bool) (xs ys : List A) :
    ((framedListEncoding e).encode xs).length≤((framedListEncoding e).encode (xs++ys)).length := by
  induction xs with
  | nil =>
    have h := framedListEncoding_length_lower e ys
    simp only [List.nil_append,framedListEncoding,framedListEncode,List.length_singleton] at h ⊢
    omega
  | cons x xs ih =>
    simp only [List.cons_append,framedListEncoding,framedListEncode,List.length_cons,
      List.length_append] at ih ⊢
    omega
theorem fixed_size (c : CoordinateQuery) (p q : ℕ) :
    InputBounds.size c.1.val≤InputBounds.size (ExactPointRecovery.ThresholdProgram.fixedValue (c,p,q)).val := by
  have hr := append_word rowEncoding c.1.val.rows [ExactPointRecovery.ThresholdProgram.front (c.1.val,c.2.val,p,q)]
  have hb := append_word IntegerArithmetic.encoding c.1.val.rhs [(p:ℤ)]
  change (rowsEncoding.encode c.1.val.rows).length ≤
    (rowsEncoding.encode (c.1.val.rows ++ [ExactPointRecovery.ThresholdProgram.front
      (c.1.val,c.2.val,p,q)])).length at hr
  change (rowEncoding.encode c.1.val.rhs).length ≤
    (rowEncoding.encode (c.1.val.rhs ++ [(p:ℤ)])).length at hb
  rw [InputBounds.length_formula,InputBounds.length_formula]
  change 2*c.1.val.rowCount+2*c.1.val.dimension+
    2*(rowsEncoding.encode c.1.val.rows).length+(rowEncoding.encode c.1.val.rhs).length+3≤
    2*(c.1.val.rowCount+1)+2*c.1.val.dimension+
    2*(rowsEncoding.encode (c.1.val.rows++[ExactPointRecovery.ThresholdProgram.front
      (c.1.val,c.2.val,p,q)])).length+
      (rowEncoding.encode (c.1.val.rhs++[(p:ℤ)])).length+3
  omega
theorem denominator (d e : Raw) (h : InputBounds.size d≤InputBounds.size e) :
    InputBounds.denominator d≤InputBounds.denominator e := by
  unfold InputBounds.denominator
  apply Nat.pow_le_pow_right (by decide)
  have hs := Nat.mul_le_mul h h
  nlinarith
end Monotone
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
