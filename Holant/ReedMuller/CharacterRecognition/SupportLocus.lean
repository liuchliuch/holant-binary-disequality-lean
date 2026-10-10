import Holant.ReedMuller.CharacterRecognition.SupportSelfDual
import Holant.ReedMuller.CharacterRecognition.SignedCards

/-! The actual signed cards force every supported orbit numerator to be
identically zero or nonzero on the entire original affine support. A proper
phase hyperplane would lose one more quotient dimension. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.CharacterFlat SignedTransport
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- Both signs and both layers in one actual frame per accessible direction. -/
def CFlatSignedRadonCards (g : BinaryVector n → ℂ) : Prop :=
  ∀ v : BinaryVector n,Accessible v → ∃ F : RadonAccess.RadonFrame n,F.v=v ∧
    ∀ d l,CFlat (fun x => actualSignedRadon F d l g (vectorWord x))

theorem CFlatSignedRadonCards.plus {g : BinaryVector n → ℂ}
    (h : CFlatSignedRadonCards g) : CFlatRadonCards g := by
  intro v hv
  obtain ⟨F,hF,hcards⟩ := h v hv
  exact ⟨F,hF,fun d => by simpa only [actualSignedRadon_plus] using hcards d 0⟩

namespace SignedTransport

 theorem signed_orbit_affine_support (F : RadonAccess.RadonFrame n) (d l : ZMod 2)
    (g : BinaryVector n → ℂ) (a y0 : BinaryVector n) (D : BinaryCode n)
    (hg : ∀ y,g y+sign l*g (y+F.v)≠0 ↔ y-a∈D)
    (hy0 : y0-a∈D) (hl0 : dot y0 F.v=d) :
    ∀ x,actualSignedRadon F d l g x≠0 ↔
      x-AffineRadon.RadonFrame.boundaryProjection F y0∈
        AffineRadon.RadonFrame.projectedLayerDirection F D := by
  intro x
  rw [←AffineRadon.RadonFrame.affine_layer_image F d a y0 D hy0 hl0]
  constructor
  · intro h
    refine ⟨AffineRadon.RadonFrame.boundaryLift F d x,?_,
      AffineRadon.RadonFrame.boundaryLift_layer F d x,
      AffineRadon.RadonFrame.boundaryLift_projection F d x⟩
    exact (hg _).mp ((actualSignedRadon_nonzero_iff F d l g x).mp h)
  · rintro ⟨y,hy,hl,hp⟩
    have hh := actualSignedRadon_projection F d l g y hl
    rw [hp] at hh
    rw [hh,mul_ne_zero_iff]
    exact ⟨sign_nonzero _,(hg y).mpr hy⟩

 theorem signed_orbit_character_card_dimension (F : RadonAccess.RadonFrame n) (d l : ZMod 2)
    (g : BinaryVector n → ℂ) (a y0 : BinaryVector n) (D : BinaryCode n)
    (hg : ∀ y,g y+sign l*g (y+F.v)≠0 ↔ y-a∈D)
    (hy0 : y0-a∈D) (hl0 : dot y0 F.v=d)
    (hflat : CFlat (fun x => actualSignedRadon F d l g (vectorWord x))) :
    2*Module.finrank (ZMod 2) (AffineRadon.RadonFrame.projectedLayerDirection F D)=n-2 := by
  have hs := signed_orbit_affine_support F d l g a y0 D hg hy0 hl0
  have hn : (fun x => actualSignedRadon F d l g (vectorWord x))≠0 := by
    intro hz
    have hh := congrFun hz (wordVector (AffineRadon.RadonFrame.boundaryProjection F y0))
    exact ((hs (AffineRadon.RadonFrame.boundaryProjection F y0)).mpr (by simp))
      (by simpa only [vector_word,Pi.zero_apply] using hh)
  apply nonzeroFlat_support_dimension _ (hflat.resolve_left hn)
    (AffineRadon.RadonFrame.boundaryProjection F y0)
  intro x
  simpa only [vector_word] using hs x

end SignedTransport
end
end Holant.ReedMuller.CharacterRecognition

namespace Holant.ReedMuller.AffineRadon
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
open Holant.ReedMuller.CharacterRecognition Holant.ReedMuller.CharacterRecognition.SignedTransport
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ} {f : Signature AlgebraicComplex (2*r)}

/-- For every actual signed orbit, character-flatness excludes the proper
phase-cut alternative. The surviving locus is exactly the original support. -/
theorem ActualNormalForm.signed_orbit_zero_or_full_character (hr : 4≤r)
    (A : ActualNormalForm f)
    (hd : CFlatSignedRadonCards (fun x => (f (wordVector x):ℂ)))
    (v : BinaryVector (2*r)) (hv : Accessible v) (hvU : v∈A.direction) (l : ZMod 2) :
    (∀ x,(f (wordVector x):ℂ)+sign l*(f (wordVector (x+v)):ℂ)=0) ∨
    (∀ x,(f (wordVector x):ℂ)+sign l*(f (wordVector (x+v)):ℂ)≠0 ↔
      x-A.shift∈A.direction) := by
  have hU := A.direction_selfDual_character hr hd.plus
  have hRank := A.support_half_rank_character hr hd.plus
  obtain ⟨F,hF,hflat⟩ := hd v hv
  rcases A.complex_signed_locus v hvU l with hz|hs|⟨b,D,hb,hDU,hvD,hDim,hD⟩
  · exact Or.inl hz
  · exact Or.inr hs
  · let g : BinaryVector (2*r) → ℂ := fun x => (f (wordVector x):ℂ)
    have hsp : ∀ x,g x+sign l*g (x+F.v)≠0 ↔ x-b∈D := by
      simpa only [hF,g] using hD
    have hc := signed_orbit_character_card_dimension F (dot b F.v) l
      g b b D hsp (by simp) rfl (hflat _ _)
    have hDp : ∀ x,x∈D → dot x F.v=0 := by
      intro x hx
      rw [hF]
      exact (hU x).mp (hDU hx) v hvU
    have hDv : F.v∈D := by simpa only [hF] using hvD
    have hproj := RadonFrame.projectedLayerDimension_add_one_of_perpendicular_mem F D hDp hDv
    omega

end
end Holant.ReedMuller.AffineRadon
