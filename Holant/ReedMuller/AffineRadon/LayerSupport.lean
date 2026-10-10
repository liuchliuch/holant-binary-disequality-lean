import Holant.ReedMuller.AffineRadon.NoCancellation
import Holant.ReedMuller.AffineRadon.LayerDimension

/-! The actual nonempty affine layer projects to the literal mapped direction.
For nonoverlapping Radon lifts this is the exact tensor support, so a flat-card
hypothesis yields the source dimension equations without an assumed support. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
namespace RadonFrame

 theorem affine_layer_image (F : RadonAccess.RadonFrame n) (ε : ZMod 2)
    (a y0 : BinaryVector n) (U : BinaryCode n) (hy0 : y0-a∈U)
    (hl0 : dot y0 F.v=ε) (x : BinaryVector (n-2)) :
    (∃ y : BinaryVector n,y-a∈U ∧ dot y F.v=ε ∧ boundaryProjection F y=x) ↔
      x-boundaryProjection F y0∈projectedLayerDirection F U := by
  rw [mem_projectedLayerDirection]
  constructor
  · rintro ⟨y,hy,hl,hp⟩
    refine ⟨y-y0,⟨?_,?_⟩,?_⟩
    · have H := U.sub_mem hy hy0
      have he : (y-a)-(y0-a)=y-y0 := by abel
      rwa [he] at H
    · have he : dot (y-y0) F.v=dot y F.v-dot y0 F.v := by
        simp [dot,sub_mul,Finset.sum_sub_distrib]
      rw [he,hl,hl0,sub_self]
    · rw [map_sub,hp]
  · rintro ⟨u,⟨hu,hl⟩,hp⟩
    refine ⟨y0+u,?_,?_,?_⟩
    · have H := U.add_mem hy0 hu
      have he : (y0-a)+u=y0+u-a := by abel
      rwa [he] at H
    · rw [dot_add_left,hl0,hl,add_zero]
    · rw [map_add,hp]
      abel

 theorem actualRadon_affine_support_no_overlap (F : RadonAccess.RadonFrame n) (ε : ZMod 2)
    (g : BinaryVector n → ℂ) (a y0 : BinaryVector n) (U : BinaryCode n)
    (hg : exactSupport g a U) (hv : F.v∉U) (hy0 : y0-a∈U) (hl0 : dot y0 F.v=ε) :
    ∀ x,actualRadon F ε g x≠0 ↔ x-boundaryProjection F y0∈projectedLayerDirection F U := by
  intro x
  rw [actualRadon_support_no_overlap F ε g a U hg hv,
    affine_layer_image F ε a y0 U hy0 hl0]

 theorem nonoverlap_flat_card_dimension (F : RadonAccess.RadonFrame n) (ε : ZMod 2)
    (g : BinaryVector n → ℂ) (a y0 : BinaryVector n) (U : BinaryCode n)
    (hg : exactSupport g a U) (hv : F.v∉U) (hy0 : y0-a∈U) (hl0 : dot y0 F.v=ε)
    (hflat : FlatOrZero (fun x => actualRadon F ε g (vectorWord x))) :
    2*Module.finrank (ZMod 2) (projectedLayerDirection F U)=n-2 := by
  have hs := actualRadon_affine_support_no_overlap F ε g a y0 U hg hv hy0 hl0
  have hn : (fun x => actualRadon F ε g (vectorWord x))≠0 := by
    intro hz
    have H := congrFun hz (wordVector (boundaryProjection F y0))
    have hh := (hs (boundaryProjection F y0)).mpr (by simp)
    exact hh (by simpa only [vector_word,Pi.zero_apply] using H)
  have hf := hflat.resolve_left hn
  apply flat_support_dimension _ hf (boundaryProjection F y0)
  intro x
  simpa only [vector_word] using hs x

 theorem nonoverlap_dimension_cases {r : ℕ} (hr : 1≤r) (F : RadonAccess.RadonFrame (2*r))
    (g : BinaryVector (2*r) → ℂ) (a : BinaryVector (2*r)) (U : BinaryCode (2*r))
    (hg : exactSupport g a U) (hv : F.v∉U)
    (hflat : ∀ ε,FlatOrZero (fun x => actualRadon F ε g (vectorWord x))) :
    ( (∀ x,x∈U → dot x F.v=0) ∧ Module.finrank (ZMod 2) U=r-1) ∨
    (¬(∀ x,x∈U → dot x F.v=0) ∧ Module.finrank (ZMod 2) U=r) := by
  have hc := nonoverlap_flat_card_dimension F (dot a F.v) g a a U hg hv (by simp) rfl (hflat _)
  have hp := projectedLayerDimension_of_not_mem F U hv
  by_cases hU : ∀ x,x∈U → dot x F.v=0
  · left
    have hl := layerDimension_of_perpendicular F U hU
    exact ⟨hU,by omega⟩
  · right
    have hl := layerDimension_add_one_of_not_perpendicular F U hU
    exact ⟨hU,by omega⟩

end RadonFrame
end
end Holant.ReedMuller.AffineRadon
