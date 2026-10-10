import Holant.ReedMuller.AffineRadon.FlatIsometry
import Holant.ReedMuller.AffineRadon.NoCancellation
import Holant.ReedMuller.SignedRadon.Source

/-! The normalized quotient cards in7.19 are exactly the actual native-X
signed-card networks at sign zero, after a proved surviving-coordinate affine
isometry and removal of recorded nonzero representative scalars. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 theorem flat_nonzero_smul (f : Signature ℂ n) (hf : Flat f) (c : ℂ) (hc : c≠0) : Flat (c • f) := by
  obtain ⟨d,a,D,hD,rfl⟩ := hf
  refine ⟨Units.mk0 c hc*d,a,D,hD,?_⟩
  funext x
  simp only [Pi.smul_apply,smul_eq_mul,flatSignature,Units.val_mul,Units.val_mk0]
  split_ifs <;> ring

 theorem flatOrZero_nonzero_smul (f : Signature ℂ n) (hf : FlatOrZero f) (c : ℂ) (hc : c≠0) :
    FlatOrZero (c • f) := by
  rcases hf with rfl | hf
  · exact Or.inl (smul_zero c)
  · exact Or.inr (flat_nonzero_smul f hf c hc)

namespace RadonFrame

def pairToOrdinary (F : RadonAccess.RadonFrame (n+2)) : BinaryVector n ≃ₗ[ZMod 2] BinaryVector (n+2-2) :=
  F.pairBoundaryLinearEquiv.symm.trans F.ordinaryBoundaryLinearEquiv

 theorem pairToOrdinary_isometry (F : RadonAccess.RadonFrame (n+2)) (x y : BinaryVector n) :
    dot (pairToOrdinary F x) (pairToOrdinary F y)=dot x y := by
  have h1 := F.ordinaryBoundaryLinearEquiv_isometry (F.pairBoundaryLinearEquiv.symm x)
    (F.pairBoundaryLinearEquiv.symm y)
  have h2 := F.pairBoundaryLinearEquiv_isometry (F.pairBoundaryLinearEquiv.symm x)
    (F.pairBoundaryLinearEquiv.symm y)
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at h2
  exact h1.trans h2.symm

 theorem actualRadon_eq_physical_coordinates (F : RadonAccess.RadonFrame (n+2))
    (g : Signature ℂ (n+2)) (d : ZMod 2) :
    (fun x => actualRadon F d (fun y => g (wordVector y)) (vectorWord x))=
      affineIsometryPullback (pairToOrdinary F) (pairToOrdinary F (ones n))
        (SignedRadon.RadonFrame.boundaryCard F d 0 g) := by
  funext x
  simp only [affineIsometryPullback,SignedRadon.RadonFrame.boundaryCard_apply,
    vector_word,zero_mul,CharacterFlat.sign_zero,one_mul]
  have he : F.pairBoundaryLinearEquiv.symm
      ((pairToOrdinary F).symm (vectorWord x-pairToOrdinary F (ones n))+ones n)=
      F.ordinaryBoundaryLinearEquiv.symm (vectorWord x) := by
    rw [map_sub,LinearEquiv.symm_apply_apply,sub_add_cancel]
    change F.pairBoundaryLinearEquiv.symm
      (F.pairBoundaryLinearEquiv (F.ordinaryBoundaryLinearEquiv.symm (vectorWord x)))=_
    exact F.pairBoundaryLinearEquiv.symm_apply_apply _
  simp only [SignedRadon.RadonFrame.boundaryLift,he]
  rfl

 theorem flat_physical_coordinates_implies_actualRadon (F : RadonAccess.RadonFrame (n+2))
    (g : Signature ℂ (n+2)) (d : ZMod 2)
    (hf : FlatOrZero (SignedRadon.RadonFrame.boundaryCard F d 0 g)) :
    FlatOrZero (fun x => actualRadon F d (fun y => g (wordVector y)) (vectorWord x)) := by
  rw [actualRadon_eq_physical_coordinates]
  exact flatOrZero_affineIsometryPullback _ (pairToOrdinary_isometry F) _ _ hf

 theorem flat_native_network_implies_actualRadon {κ : ZMod 2 → ZMod 2 → ℂ}
    (hκ : ∀ d l,κ d l≠0) (F : RadonAccess.RadonFrame (n+2)) (Γ : SignedRadon.ActualGraph κ F.A)
    (g : Signature ℂ (n+2)) (d : ZMod 2)
    (hf : FlatOrZero (SignedRadon.signedNetwork F Γ g d 0).denote) :
    FlatOrZero (fun x => actualRadon F d (fun y => g (wordVector y)) (vectorWord x)) := by
  rw [SignedRadon.signedNetwork_denote] at hf
  have hc : Γ.scalar*κ d 0≠0 := mul_ne_zero Γ.scalar_ne (hκ d 0)
  have H := flatOrZero_nonzero_smul _ hf (Γ.scalar*κ d 0)⁻¹ (inv_ne_zero hc)
  rw [smul_smul,inv_mul_cancel₀ hc,one_smul] at H
  exact flat_physical_coordinates_implies_actualRadon F g d H

end RadonFrame
end
end Holant.ReedMuller.AffineRadon
