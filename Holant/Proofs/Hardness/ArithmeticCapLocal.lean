import Holant.Proofs.Hardness.GeneralGeometricCapLocal
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! An arithmetic cap criterion independent of norm dominance. A nonintegral
ratio cannot have a positive power equal to one. In particular equal-modulus
complex caps may support global interpolation despite local pin obstructions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ArithmeticCapLocal
open Holant
namespace Cap
export GeneralCancellationCapPin (Choice oriented)
end Cap
variable {K : Type} [Field K]

def Applicable (M : Signature K 4) : Prop :=
  ∃i : Cap.Choice,(Cap.oriented M i).1≠0 ∧ (Cap.oriented M i).2≠0 ∧
    ¬IsIntegral ℤ ((Cap.oriented M i).1/(Cap.oriented M i).2)

theorem infinite_of_nonintegral (r : K) (h : ¬IsIntegral ℤ r)
    (n : ℕ) (hn : 0<n) : r^n≠1 := by
  intro he
  apply h
  apply IsIntegral.of_pow hn
  rw [he]
  exact isIntegral_one

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ArithmeticCapLocal
