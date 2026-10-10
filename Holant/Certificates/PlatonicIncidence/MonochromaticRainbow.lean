import Holant.Certificates.PlatonicIncidence.MonochromaticProjective

/-! Bridge from the exhaustive matching-line classification to the frozen
semantic rainbow-line API. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matchingSecant_collinear_points (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (S : Finset (MatchingIndex ι)) (hS : MatchingSecant K S) :
    Projectivization.IsCollinear (configurationPoints K hdet S : Set Point) := by
  classical
  obtain ⟨p,q,hpq,hspan⟩ := hS
  refine ⟨(Submodule.span ℂ ({configurationTensor K p,configurationTensor K q} : Set FourTensor)).projectivization,
    ?_,?_,?_⟩
  · rw [Projectivization.Subspace.submodule.apply_symm_apply]
    exact Module.Finite.span_of_finite _ (Set.toFinite _)
  · rw [Projectivization.Subspace.submodule.apply_symm_apply,configuration_pair_finrank K hdet hfaith p q hpq]
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact (Submodule.mk_mem_projectivization_iff _ _).mpr ((hspan x).mp hx)

theorem matchingSecant_familyRainbow (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (G : BinaryMatrix→Prop) (hG : ∀i,G (K i))
    (S : Finset (MatchingIndex ι)) (hS : MatchingSecant K S)
    (hlabels : ∀r : Fin 3,∃!p,p∈S ∧ p.1=r) :
    FamilyRainbowLine G (configurationPoints K hdet S) := by
  classical
  let q : Fin 3→MatchingIndex ι := fun r => Classical.choose (hlabels r)
  have hq (r : Fin 3) : q r∈S ∧ (q r).1=r := (Classical.choose_spec (hlabels r)).1
  have hunique (r : Fin 3) (p : MatchingIndex ι) (hp : p∈S) (hpr : p.1=r) : p=q r :=
    (Classical.choose_spec (hlabels r)).2 p ⟨hp,hpr⟩
  let p : Fin 3→Point := fun r => configurationPoint K hdet (q r)
  have hpoints : configurationPoints K hdet S=points p := by
    ext z
    simp only [configurationPoints,points,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x.1,?_⟩
      change configurationPoint K hdet (q x.1)=configurationPoint K hdet x
      rw [←hunique x.1 x hx rfl]
    · rintro ⟨r,rfl⟩
      exact ⟨q r,(hq r).1,rfl⟩
  refine ⟨p,⟨?_,?_⟩,hpoints⟩
  · intro r
    refine ⟨configurationTensor K (q r),configurationTensor_nonzero K hdet (q r),?_,rfl⟩
    refine ⟨K (q r).2.1,K (q r).2.2,hG _,hG _,?_⟩
    simp only [configurationTensor,(hq r).2]
  · have hc := matchingSecant_collinear_points K hdet hfaith S hS
    rw [hpoints] at hc
    apply Projectivization.isCollinear_subset _ _ ?_ hc
    intro z hz
    rcases hz with rfl|rfl|hz
    · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
    · rcases hz with rfl
      exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,rfl⟩

/-- Every actual rich projective line is a complete one-factor ruling or an
A.18 semantic rainbow, with all matching labels retained. -/
theorem actualRichLine_mono_or_rainbow (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (G : BinaryMatrix→Prop) (hG : ∀i,G (K i))
    (Q : Finset Point) (hQ : ActualRichLine K hdet Q) :
    (∃ r b f L,BinarySecant K L ∧ 3≤L.card ∧ Q=configurationPoints K hdet (rulingSet r b f L)) ∨
      FamilyRainbowLine G Q := by
  obtain ⟨S,hS,hc,rfl⟩ := (actualRichLine_iff K hdet hfaith Q).mp hQ
  rcases matchingSecant_classification K hdet hfaith S hS hc with h|h
  · obtain ⟨r,b,f,L,hL,hcL,rfl⟩ := h
    exact Or.inl ⟨r,b,f,L,hL,hcL,rfl⟩
  · exact Or.inr (matchingSecant_familyRainbow K hdet hfaith G hG S hS h.2)

end
end Holant.Certificates.PlatonicIncidence
