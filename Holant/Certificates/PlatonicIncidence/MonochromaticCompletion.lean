import Holant.Certificates.PlatonicIncidence.MonochromaticMaximal
import Holant.Certificates.PlatonicIncidence.MonochromaticTransport

/-! Exhaustive and disjoint classification of actual maximal rich lines,
including the frozen A.18 semantic rainbow family. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem familyRainbow_injective (G : BinaryMatrix→Prop)
    (hdet : ∀{U : BinaryMatrix},G U→U.det≠0)
    (p : Fin 3→Point) (hp : FamilyRainbow G p) : Function.Injective p := by
  intro r s he
  obtain ⟨F,hF,⟨U,V,hU,hV,rfl⟩,heF⟩ := hp.1 r
  obtain ⟨H,hH,⟨S,T,hS,hT,rfl⟩,heH⟩ := hp.1 s
  rw [heF,heH] at he
  exact proportional_matching_labels r s U V S T (hdet hU) (hdet hV) (hdet hS) (hdet hT)
    ((proportional_point_iff _ _ hF hH).mpr he)

theorem familyRainbowLine_actualRichLine (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (G : BinaryMatrix→Prop) (hG : ∀i,G (K i))
    (hGdet : ∀{U : BinaryMatrix},G U→U.det≠0)
    (hcomplete : ∀U,G U→∃i,Proportional U (K i))
    (Q : Finset Point) (hQ : FamilyRainbowLine G Q) : ActualRichLine K hdet Q := by
  classical
  apply (actualRichLine_iff_maximal K hdet hfaith Q).mpr
  have hmax := hQ.maximal hGdet
  obtain ⟨p,hp,rfl⟩ := hQ
  have hdeck (r : Fin 3) : FamilyDeckPoint G (p r) := by
    obtain ⟨F,hF,hm,he⟩ := hp.1 r
    exact ⟨r,F,hF,hm,he⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro z hz
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hz
    exact (configurationDeck_iff_familyDeckPoint K hdet G hG hcomplete _).mpr (hdeck r)
  · have hc : (points p).card=3 := by
      simp [points,Finset.card_image_of_injective _ (familyRainbow_injective G hGdet p hp)]
    omega
  · have he : (points p : Set Point)={p 0,p 1,p 2} := by
      simp [points,←range_three]
    rw [he]
    exact hp.2
  · intro z hz hc
    exact hmax z ((configurationDeck_iff_familyDeckPoint K hdet G hG hcomplete z).mp hz) hc

theorem familyRainbowLine_not_one_matching (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (G : BinaryMatrix→Prop)
    (hcomplete : ∀U,G U→∃i,Proportional U (K i))
    (Q : Finset Point) (hQ : FamilyRainbowLine G Q) : ¬ActualOneMatching K hdet Q := by
  classical
  obtain ⟨p,hp,rfl⟩ := hQ
  rintro ⟨s,hs⟩
  have hlabel (r : Fin 3) : r=s := by
    obtain ⟨F,hF,⟨U,V,hU,hV,rfl⟩,he⟩ := hp.1 r
    obtain ⟨i,hi⟩ := hcomplete U hU
    obtain ⟨j,hj⟩ := hcomplete V hV
    have hpoint : p r=configurationPoint K hdet (r,i,j) := by
      rw [he]
      exact (proportional_point_iff _ _ _ _).mp (matching_proportional r hi hj)
    apply hs (r,i,j)
    rw [←hpoint]
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
  have hz := (hlabel 0).trans (hlabel 1).symm
  exact (by decide : (0 : Fin 3)≠1) hz

/-- No actual maximal rich line falls outside the two source families, and
every line in either family is an actual maximal rich line. -/
theorem actualRichLine_complete_iff (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (G : BinaryMatrix→Prop) (hG : ∀i,G (K i))
    (hGdet : ∀{U : BinaryMatrix},G U→U.det≠0)
    (hcomplete : ∀U,G U→∃i,Proportional U (K i))
    (D : Finset (Finset ι)) (hD : ∀L,L∈D ↔ BinarySecant K L ∧ 3≤L.card)
    (Q : Finset Point) :
    ActualRichLine K hdet Q ↔ Q∈actualMonochromaticLines K hdet D ∨ FamilyRainbowLine G Q := by
  classical
  constructor
  · intro hQ
    rcases actualRichLine_mono_or_rainbow K hdet hfaith G hG Q hQ with h|h
    · obtain ⟨r,b,f,L,hL,hc,rfl⟩ := h
      left
      apply Finset.mem_image.mpr
      refine ⟨rulingSet r b f L,?_,rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨(r,b,f,L),?_,rfl⟩
      simpa [rulingParameters] using (hD L).mpr ⟨hL,hc⟩
    · exact Or.inr h
  · rintro (h|h)
    · exact ((actualMonochromaticLines_exact K hdet hfaith D hD Q).mp h).1
    · exact familyRainbowLine_actualRichLine K hdet hfaith G hG hGdet hcomplete Q h

theorem actual_monochromatic_rainbow_disjoint (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (G : BinaryMatrix→Prop) (hcomplete : ∀U,G U→∃i,Proportional U (K i))
    (D : Finset (Finset ι)) (hD : ∀L,L∈D ↔ BinarySecant K L ∧ 3≤L.card)
    (Q : Finset Point) (hQ : Q∈actualMonochromaticLines K hdet D) : ¬FamilyRainbowLine G Q := by
  intro h
  exact familyRainbowLine_not_one_matching K hdet G hcomplete Q h
    ((actualMonochromaticLines_exact K hdet hfaith D hD Q).mp hQ).2

/-- The semantic set of actual monochromatic maximal rich lines has the
same exact cardinality as the derived finite enumeration. -/
theorem actual_monochromatic_ncard (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (D : Finset (Finset ι)) (hD : ∀L,L∈D ↔ BinarySecant K L ∧ 3≤L.card) (n : ℕ) :
    {Q : Finset Point | ActualRichLine K hdet Q ∧ ActualOneMatching K hdet Q ∧ Q.card=n}.ncard=
      6*Fintype.card ι*(D.filter (fun L => L.card=n)).card := by
  classical
  have he : {Q : Finset Point | ActualRichLine K hdet Q ∧ ActualOneMatching K hdet Q ∧ Q.card=n}=
      ((actualMonochromaticLines K hdet D).filter (fun Q => Q.card=n) : Set (Finset Point)) := by
    ext Q
    simp only [Finset.mem_coe,Finset.mem_filter,actualMonochromaticLines_exact K hdet hfaith D hD Q,
      Set.mem_setOf_eq,and_assoc]
  rw [he,Set.ncard_coe_finset]
  exact actualMonochromaticLines_filter_card K hdet hfaith D
    (fun L hL => le_trans (by decide : 2≤3) ((hD L).mp hL).2) n

end
end Holant.Certificates.PlatonicIncidence
