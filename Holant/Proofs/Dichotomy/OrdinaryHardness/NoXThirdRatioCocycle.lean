import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalMergeFailure

/-! Exact multiplicative three-cube identities. Splitting a direction into
two actual Boolean directions uses a telescoping ratio, with all nonzero
coefficients explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXThirdRatioCocycle
open Holant Holant.Tractable Holant.Tractable.AffinePhase
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {n : ℕ} (f : Signature AlgebraicComplex n) (full : ∀x,f x≠0)

include full

theorem second_nonzero (z u v : Word n) : secondRatio f z u v≠0 := by
  exact div_ne_zero (mul_ne_zero (full _) (full _)) (mul_ne_zero (full _) (full _))

theorem delta (z u v w : Word n) :
    thirdRatio f z u v w=secondRatio f (xor z u) v w/secondRatio f z v w := by
  simp only [thirdRatio,secondRatio]
  field_simp [full]

theorem direction_sum (z u v b c : Word n) :
    thirdRatio f z (xor u v) b c=thirdRatio f z u b c*thirdRatio f (xor z u) v b c := by
  rw [delta f full,delta f full,delta f full,←xor_assoc]
  field_simp [second_nonzero f full]

theorem shift_first (z u v w : Word n) :
    thirdRatio f (xor z u) u v w=(thirdRatio f z u v w)⁻¹ := by
  rw [delta f full,delta f full,xor_assoc,AffinePhase.xor_self,xor_origin]
  exact (inv_div _ _).symm


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXThirdRatioCocycle
end
