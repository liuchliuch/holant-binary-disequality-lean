import Holant.ReedMuller.AffinePatching.ReconstructionSupport
import Holant.ReedMuller.AffinePatching.AffineSupport

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSquareSupport
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (f : Signature AlgebraicComplex n)
variable (hs : Affine (fun x=>f x^2)) (hn : f≠0)

include hs hn in
theorem exists_support_system : ∃S : AffineSystem n,∀x,S.Holds x ↔ f x≠0 := by
  rcases hs with hz | ⟨c,hc,S,Q,he⟩
  · exfalso
    apply hn
    funext x
    have h := congrFun hz x
    exact (pow_eq_zero_iff (by decide : 2≠0)).mp h
  · refine ⟨S,fun x=>?_⟩
    have h := congrFun he x
    change f x^2=affineFormula c S Q x at h
    constructor
    · intro hx hz
      rw [hz] at h
      exact (mul_ne_zero hc (fourthRootPhase_ne_zero _)) (by simpa [affineFormula,hx] using h.symm)
    · intro hx
      by_contra hS
      have hz : f x^2=0 := h.trans (by simp [affineFormula,hS])
      exact (pow_ne_zero 2 hx) hz


include hn in
theorem exists_base : ∃x,f x≠0 := by
  by_contra! h
  exact hn (funext h)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSquareSupport
end
