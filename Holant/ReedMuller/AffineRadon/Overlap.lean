import Holant.ReedMuller.AffineRadon.LayerSupport

/-! Exact support of overlapping Radon orbits after the actual coefficient
sum has been classified. No factor or quotient-support witness is assumed. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
namespace RadonFrame

 theorem actualRadon_projection (F : RadonAccess.RadonFrame n) (g : BinaryVector n → ℂ)
    (y : BinaryVector n) :
    actualRadon F (dot y F.v) g (boundaryProjection F y)=g y+g (y+F.v) := by
  rcases (boundary_fiber F (dot y F.v) (boundaryProjection F y) y rfl).mp rfl with h | h
  · conv_rhs => rw [h]
    rfl
  · unfold actualRadon
    conv_rhs => rw [h]
    simp only [add_assoc,RadonAccess.binary_add_self,add_zero]
    exact add_comm _ _

 theorem actualRadon_support_of_orbit_support (F : RadonAccess.RadonFrame n) (ε : ZMod 2)
    (g : BinaryVector n → ℂ) (a y0 : BinaryVector n) (D : BinaryCode n)
    (hg : ∀ y,g y+g (y+F.v)≠0 ↔ y-a∈D)
    (hy0 : y0-a∈D) (hl0 : dot y0 F.v=ε) :
    ∀ x,actualRadon F ε g x≠0 ↔ x-boundaryProjection F y0∈projectedLayerDirection F D := by
  intro x
  rw [←affine_layer_image F ε a y0 D hy0 hl0]
  constructor
  · intro h
    exact ⟨boundaryLift F ε x,(hg _).mp h,boundaryLift_layer F ε x,boundaryLift_projection F ε x⟩
  · rintro ⟨y,hy,hl,hp⟩
    have H := actualRadon_projection F g y
    rw [hl,hp] at H
    rw [H]
    exact (hg y).mpr hy

 theorem orbit_support_flat_card_dimension (F : RadonAccess.RadonFrame n) (ε : ZMod 2)
    (g : BinaryVector n → ℂ) (a y0 : BinaryVector n) (D : BinaryCode n)
    (hg : ∀ y,g y+g (y+F.v)≠0 ↔ y-a∈D)
    (hy0 : y0-a∈D) (hl0 : dot y0 F.v=ε)
    (hflat : FlatOrZero (fun x => actualRadon F ε g (vectorWord x))) :
    2*Module.finrank (ZMod 2) (projectedLayerDirection F D)=n-2 := by
  have hs := actualRadon_support_of_orbit_support F ε g a y0 D hg hy0 hl0
  have hn : (fun x => actualRadon F ε g (vectorWord x))≠0 := by
    intro hz
    have H := congrFun hz (wordVector (boundaryProjection F y0))
    have hh := (hs (boundaryProjection F y0)).mpr (by simp)
    exact hh (by simpa only [vector_word,Pi.zero_apply] using H)
  apply flat_support_dimension _ (hflat.resolve_left hn) (boundaryProjection F y0)
  intro x
  simpa only [vector_word] using hs x

 theorem orbit_support_flat_card_selfDual (F : RadonAccess.RadonFrame n) (ε : ZMod 2)
    (g : BinaryVector n → ℂ) (a y0 : BinaryVector n) (D : BinaryCode n)
    (hg : ∀ y,g y+g (y+F.v)≠0 ↔ y-a∈D)
    (hy0 : y0-a∈D) (hl0 : dot y0 F.v=ε)
    (hflat : FlatOrZero (fun x => actualRadon F ε g (vectorWord x))) :
    SelfDual (projectedLayerDirection F D) := by
  have hs := actualRadon_support_of_orbit_support F ε g a y0 D hg hy0 hl0
  have hn : (fun x => actualRadon F ε g (vectorWord x))≠0 := by
    intro hz
    have H := congrFun hz (wordVector (boundaryProjection F y0))
    have hh := (hs (boundaryProjection F y0)).mpr (by simp)
    exact hh (by simpa only [vector_word,Pi.zero_apply] using H)
  apply flat_support_selfDual _ (hflat.resolve_left hn) (boundaryProjection F y0)
  intro x
  simpa only [vector_word] using hs x

end RadonFrame
end
end Holant.ReedMuller.AffineRadon
