import Holant.ReedMuller.CharacterFlat.Basic
import Holant.ReedMuller.AffineRadon.Deck

/-! Support geometry of actual character-flat Radon cards. A nonconstant sign
character changes coefficients but never its exact affine support. These
wrappers reuse the frozen affine geometry without any coefficient-constant
hypothesis. Both zero and nonzero cards remain part of the literal input. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffineRadon
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- The direction of any exact affine description of a character-flat support
is the original self-dual direction, even for a nonconstant character. -/
theorem nonzeroFlat_support_selfDual (f : Signature ℂ n) (hf : NonzeroFlat f)
    (a : BinaryVector n) (D : BinaryCode n)
    (hs : ∀ x,f (wordVector x)≠0 ↔ x-a∈D) : SelfDual D := by
  obtain ⟨c,b,E,ell,hE,he⟩ := hf
  have hh : ∀ x,f (wordVector x)≠0 ↔ x-b∈E := by
    intro x
    rw [he]
    simp only [signature,vector_word]
    exact value_nonzero_iff c c.ne_zero b E ell x
  have hd := affine_support_direction_unique (fun x => f (wordVector x)) a b D E hs hh
  rw [hd]
  exact hE

 theorem nonzeroFlat_support_dimension (f : Signature ℂ n) (hf : NonzeroFlat f)
    (a : BinaryVector n) (D : BinaryCode n)
    (hs : ∀ x,f (wordVector x)≠0 ↔ x-a∈D) :
    2*Module.finrank (ZMod 2) D=n :=
  selfDual_half_dimension D (nonzeroFlat_support_selfDual f hf a D hs)

end
end Holant.ReedMuller.CharacterFlat

namespace Holant.ReedMuller.AffineRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
namespace RadonFrame

 theorem nonoverlap_character_card_dimension (F : RadonAccess.RadonFrame n) (ε : ZMod 2)
    (g : BinaryVector n → ℂ) (a y0 : BinaryVector n) (U : BinaryCode n)
    (hg : exactSupport g a U) (hv : F.v∉U) (hy0 : y0-a∈U) (hl0 : dot y0 F.v=ε)
    (hflat : CFlat (fun x => actualRadon F ε g (vectorWord x))) :
    2*Module.finrank (ZMod 2) (projectedLayerDirection F U)=n-2 := by
  have hs := actualRadon_affine_support_no_overlap F ε g a y0 U hg hv hy0 hl0
  have hn : (fun x => actualRadon F ε g (vectorWord x))≠0 := by
    intro hz
    have H := congrFun hz (wordVector (boundaryProjection F y0))
    have hh := (hs (boundaryProjection F y0)).mpr (by simp)
    exact hh (by simpa only [vector_word,Pi.zero_apply] using H)
  have hf := hflat.resolve_left hn
  apply nonzeroFlat_support_dimension _ hf (boundaryProjection F y0)
  intro x
  simpa only [vector_word] using hs x

 theorem nonoverlap_character_dimension_cases {r : ℕ} (hr : 1≤r) (F : RadonAccess.RadonFrame (2*r))
    (g : BinaryVector (2*r) → ℂ) (a : BinaryVector (2*r)) (U : BinaryCode (2*r))
    (hg : exactSupport g a U) (hv : F.v∉U)
    (hflat : ∀ ε,CFlat (fun x => actualRadon F ε g (vectorWord x))) :
    ( (∀ x,x∈U → dot x F.v=0) ∧ Module.finrank (ZMod 2) U=r-1) ∨
    (¬(∀ x,x∈U → dot x F.v=0) ∧ Module.finrank (ZMod 2) U=r) := by
  have hc := nonoverlap_character_card_dimension F (dot a F.v) g a a U hg hv (by simp) rfl (hflat _)
  have hp := projectedLayerDimension_of_not_mem F U hv
  by_cases hU : ∀ x,x∈U → dot x F.v=0
  · left
    have hl := layerDimension_of_perpendicular F U hU
    exact ⟨hU,by omega⟩
  · right
    have hl := layerDimension_add_one_of_not_perpendicular F U hU
    exact ⟨hU,by omega⟩

 theorem orbit_support_character_card_dimension (F : RadonAccess.RadonFrame n) (ε : ZMod 2)
    (g : BinaryVector n → ℂ) (a y0 : BinaryVector n) (D : BinaryCode n)
    (hg : ∀ y,g y+g (y+F.v)≠0 ↔ y-a∈D)
    (hy0 : y0-a∈D) (hl0 : dot y0 F.v=ε)
    (hflat : CFlat (fun x => actualRadon F ε g (vectorWord x))) :
    2*Module.finrank (ZMod 2) (projectedLayerDirection F D)=n-2 := by
  have hs := actualRadon_support_of_orbit_support F ε g a y0 D hg hy0 hl0
  have hn : (fun x => actualRadon F ε g (vectorWord x))≠0 := by
    intro hz
    have H := congrFun hz (wordVector (boundaryProjection F y0))
    have hh := (hs (boundaryProjection F y0)).mpr (by simp)
    exact hh (by simpa only [vector_word,Pi.zero_apply] using H)
  apply nonzeroFlat_support_dimension _ (hflat.resolve_left hn) (boundaryProjection F y0)
  intro x
  simpa only [vector_word] using hs x

 theorem orbit_support_character_card_selfDual (F : RadonAccess.RadonFrame n) (ε : ZMod 2)
    (g : BinaryVector n → ℂ) (a y0 : BinaryVector n) (D : BinaryCode n)
    (hg : ∀ y,g y+g (y+F.v)≠0 ↔ y-a∈D)
    (hy0 : y0-a∈D) (hl0 : dot y0 F.v=ε)
    (hflat : CFlat (fun x => actualRadon F ε g (vectorWord x))) :
    SelfDual (projectedLayerDirection F D) := by
  have hs := actualRadon_support_of_orbit_support F ε g a y0 D hg hy0 hl0
  have hn : (fun x => actualRadon F ε g (vectorWord x))≠0 := by
    intro hz
    have H := congrFun hz (wordVector (boundaryProjection F y0))
    have hh := (hs (boundaryProjection F y0)).mpr (by simp)
    exact hh (by simpa only [vector_word,Pi.zero_apply] using H)
  apply nonzeroFlat_support_selfDual _ (hflat.resolve_left hn) (boundaryProjection F y0)
  intro x
  simpa only [vector_word] using hs x

end RadonFrame
end
end Holant.ReedMuller.AffineRadon
