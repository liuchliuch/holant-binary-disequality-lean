import Holant.ReedMuller.CharacterRecognition.SupportDeck

/-! Actual character-flat-card dimensions exclude both exceptional even-hyperplane
containments and force the original affine support to have half dimension. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterRecognition
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {r : ℕ} {f : Signature AlgebraicComplex (2*r)}

 theorem ActualNormalForm.orbit_zero_or_dimension_bound_character (hr : 1≤r) (A : ActualNormalForm f)
    (hd : CFlatRadonCards (fun x => (f (wordVector x):ℂ)))
    (v : BinaryVector (2*r)) (hv : Accessible v) (hvU : v∈A.direction) :
    (∀ x,(f (wordVector x):ℂ)+(f (wordVector (x+v)):ℂ)=0) ∨
      Module.finrank (ZMod 2) A.direction≤r+2 := by
  let g : BinaryVector (2*r) → ℂ := fun x => (f (wordVector x):ℂ)
  obtain ⟨F,hF,hflat⟩ := hd v hv
  have H := A.complex_signed_locus v hvU 0
  simp only [CharacterFlat.sign_zero,one_mul] at H
  rcases H with hz | hs | ⟨b,D,hb,hDU,hvD,hDim,hD⟩
  · exact Or.inl hz
  · right
    have hsp : ∀ x,g x+g (x+F.v)≠0 ↔ x-A.shift∈A.direction := by simpa only [hF,g] using hs
    have hc := RadonFrame.orbit_support_character_card_dimension F (dot A.shift F.v)
      g A.shift A.shift A.direction hsp (by simp) rfl (hflat _)
    have hb := RadonFrame.dimension_le_projectedLayerDimension_add_two F A.direction
    omega
  · right
    have hsp : ∀ x,g x+g (x+F.v)≠0 ↔ x-b∈D := by simpa only [hF,g] using hD
    have hc := RadonFrame.orbit_support_character_card_dimension F (dot b F.v)
      g b b D hsp (by simp) rfl (hflat _)
    have hb := RadonFrame.dimension_le_projectedLayerDimension_add_two F D
    omega

 theorem ActualNormalForm.not_evenSpace_le_direction_character (hr : 4≤r) (A : ActualNormalForm f)
    (hd : CFlatRadonCards (fun x => (f (wordVector x):ℂ))) : ¬evenSpace (2*r)≤A.direction := by
  intro hE
  have hdimE := finrank_evenSpace (by omega : 0<2*r)
  have hdim := Submodule.finrank_mono hE
  have hz : ∀ v : BinaryVector (2*r),Accessible v →
      ∀ x,(f (wordVector x):ℂ)+(f (wordVector (x+v)):ℂ)=0 := by
    intro v hv
    have hvU : v∈A.direction := hE hv.1
    rcases A.orbit_zero_or_dimension_bound_character (by omega) hd v hv hvU with h | h
    · exact h
    · omega
  obtain ⟨p,q,hp,hq,hpa,hqa,hpqa⟩ := exists_accessible_triple (evenSpace (2*r))
    (fun x hx => hx) (by omega)
  let g : BinaryVector (2*r) → ℂ := fun x => (f (wordVector x):ℂ)
  have hn : g≠0 := by
    intro h
    have hc := (A.complex_support A.shift).mpr (by simp)
    exact hc (congrFun h A.shift)
  rcases three_orbit_sums_not_all_zero g hn p q with ⟨x,hx⟩ | ⟨x,hx⟩ | ⟨x,hx⟩
  · exact hx (hz p hpa x)
  · exact hx (hz q hqa x)
  · exact hx (hz (p+q) hpqa x)

 theorem ActualNormalForm.support_half_rank_character (hr : 4≤r) (A : ActualNormalForm f)
    (hd : CFlatRadonCards (fun x => (f (wordVector x):ℂ))) :
    Module.finrank (ZMod 2) A.direction=r := by
  have hU := A.not_evenSpace_le_direction_character hr hd
  have hO := CFlatRadonCards.not_evenSpace_le_orthogonal hr _ hd A.shift A.direction A.complex_support
  obtain ⟨v,hv,hvu,hvo⟩ := exists_accessible_outside_union hr A.direction (dotOrthogonal A.direction) hU hO
  have hnot : ¬∀ x,x∈A.direction → dot x v=0 := hvo
  rcases CFlatRadonCards.dimension_cases (by omega) _ hd A.shift A.direction A.complex_support v hv hvu with h | h
  · exact False.elim (hnot h.1)
  · exact h.2

 theorem ActualNormalForm.accessible_orthogonal_mem_character (hr : 4≤r) (A : ActualNormalForm f)
    (hd : CFlatRadonCards (fun x => (f (wordVector x):ℂ))) :
    ∀ v,Accessible v → v∈dotOrthogonal A.direction → v∈A.direction := by
  intro v hv hvo
  by_contra hvu
  have hu := A.support_half_rank_character hr hd
  rcases CFlatRadonCards.dimension_cases (by omega) _ hd A.shift A.direction A.complex_support v hv hvu with h | h
  · omega
  · exact h.1 hvo

end
end Holant.ReedMuller.AffineRadon
