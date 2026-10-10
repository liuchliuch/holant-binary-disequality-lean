import Holant.Tractable.AffineOperations

/-! Multiplication by an Affine row preserves and reflects Affinity wherever
its support includes the tested row. The inverse uses a genuine scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureAffineMultiplier
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem mul_iff {n : ℕ} (f g : Signature AlgebraicComplex n)
    (hg : Affine g) (support : ∀ x, f x ≠ 0 → g x ≠ 0) :
    Affine (fun x => f x * g x) ↔ Affine f := by
  constructor
  · intro h
    by_cases zero : f = 0
    · exact zero ▸ affine_zero n
    obtain ⟨x,hx⟩ := Function.ne_iff.mp zero
    have gx : g x ≠ 0 := support x hx
    have cubic : Affine (fun y => g y * g y * g y) := (hg.mul hg).mul hg
    have ha := (h.mul cubic).scale ((g x ^ 4)⁻¹)
    convert ha using 1
    funext y
    by_cases fy : f y = 0
    · simp [fy]
    · have power := hg.fourth_power_eq y x (support y fy) gx
      change f y = (g x ^ 4)⁻¹ * ((f y * g y) * (g y * g y * g y))
      calc
        _ = (g x ^ 4)⁻¹ * (f y * g x ^ 4) := by field_simp [gx]
        _ = (g x ^ 4)⁻¹ * (f y * g y ^ 4) := by rw [power]
        _ = _ := by ring
  · intro hf
    exact hf.mul hg

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureAffineMultiplier
end
