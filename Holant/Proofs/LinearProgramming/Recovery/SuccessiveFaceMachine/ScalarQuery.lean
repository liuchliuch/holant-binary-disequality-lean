import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.Context

set_option autoImplicit false

/-! Kernel-checked recovery component. The current-face threshold loop physically produces
a dyadic interval. Its original-D scalar extraction domain is proved from
actual dyadic words and sourceSize, independent of face feasibility.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Scalar
open Holant.Algebraic Holant.Complexity Codec
noncomputable section
def intervalPayload (c : Context) : ExactPointRecovery.Payload :=
  ExactPointRecovery.payload (ExactPointRecovery.resultState c.current)
def lower (c : Context) : ℚ :=
  (ExactPointRecovery.numerator (intervalPayload c):ℚ)/ExactPointRecovery.denominator (intervalPayload c)
def upper (c : Context) : ℚ :=
  ((ExactPointRecovery.numerator (intervalPayload c):ℚ)+1)/ExactPointRecovery.denominator (intervalPayload c)
def rawQuery (c : Context) : RationalExtraction.Query :=
  ((lower c,upper c),InputBounds.denominator c.original.val)

theorem box (c : Context) : 0≤lower c ∧ lower c≤upper c ∧ upper c≤1 := by
  have hn := ExactPointRecovery.payloadAt_numerator c.current
    (ExactPointRecovery.Denominator.rounds c.current.1.val)
  have hd : (0:ℚ)<(2^ExactPointRecovery.Denominator.rounds c.current.1.val:ℕ) := by positivity
  have ha : (0:ℚ)≤ExactPointRecovery.numerator
      (ExactPointRecovery.payloadAt c.current (ExactPointRecovery.Denominator.rounds c.current.1.val)) := Nat.cast_nonneg _
  have hle : (ExactPointRecovery.numerator
      (ExactPointRecovery.payloadAt c.current (ExactPointRecovery.Denominator.rounds c.current.1.val)):ℚ)+1≤
      (2^ExactPointRecovery.Denominator.rounds c.current.1.val:ℕ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
  simp only [lower,upper,intervalPayload,ExactPointRecovery.result_exact,ExactPointRecovery.payload,
    ExactPointRecovery.stamp,ExactPointRecovery.payloadAt_denominator]
  refine ⟨div_nonneg ha hd.le,?_,?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hd.le
  · exact (div_le_one hd).mpr hle
theorem width (c : Context) : upper c-lower c<1/(InputBounds.denominator c.original.val:ℚ)^2 := by
  have hw := ExactPointRecovery.Semantics.width c.current
    (ExactPointRecovery.Denominator.rounds c.current.1.val)
  have hs := ExactPointRecovery.Denominator.isolation_width c.current.1.val
  have hD := Monotone.denominator c.original.val c.current.1.val c.sourceSize
  have hDo : (0:ℚ)<InputBounds.denominator c.original.val := by exact_mod_cast InputBounds.denominator_pos _
  have hDc : (0:ℚ)<InputBounds.denominator c.current.1.val := by exact_mod_cast InputBounds.denominator_pos _
  have hD' : (InputBounds.denominator c.original.val:ℚ)≤InputBounds.denominator c.current.1.val := by exact_mod_cast hD
  have hi : (1:ℚ)/(InputBounds.denominator c.current.1.val:ℚ)^2≤
      1/(InputBounds.denominator c.original.val:ℚ)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hDc) (sq_pos_of_pos hDo)).mpr
    nlinarith
  have he : upper c-lower c=(1:ℚ)/(2^ExactPointRecovery.Denominator.rounds c.current.1.val:ℕ) := by
    simpa only [lower,upper,intervalPayload,ExactPointRecovery.result_exact,ExactPointRecovery.payload,
      ExactPointRecovery.stamp,ExactPointRecovery.interval] using hw
  rw [he]
  exact hs.trans_le hi
def query (c : Context) : RationalExtraction.Source.Input :=
  ⟨rawQuery c,⟨⟨(box c).2.1,InputBounds.denominator_pos c.original.val⟩,width c⟩⟩
end
end Scalar
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
