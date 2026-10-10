import Holant.Certificates.PlatonicIncidence.MonochromaticCompletion
import Holant.Certificates.PlatonicIncidence.DomainCounts

namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

theorem representative_proportional_faithful (g : PlatonicModel) (i j : Fin (size g))
    (h : Proportional (representative g i) (representative g j)) : i=j := by
  obtain ⟨c,_,hc⟩ := h
  exact projectively_injective g i j c hc

def richDomainLines (g : PlatonicModel) : Finset (Finset (Fin (size g))) :=
  (domainLines g).filter (fun L => 3≤L.card)

theorem richDomainLines_exact (g : PlatonicModel) (L : Finset (Fin (size g))) :
    L∈richDomainLines g ↔ BinarySecant (representative g) L ∧ 3≤L.card := by
  rw [richDomainLines,Finset.mem_filter,domainLines_exact]
  rfl

def standardMonochromaticLines (g : PlatonicModel) : Finset (Finset Point) :=
  actualMonochromaticLines (representative g) (representative_det_ne_zero g) (richDomainLines g)

theorem standardMonochromaticLines_exact (g : PlatonicModel) (Q : Finset Point) :
    Q∈standardMonochromaticLines g ↔
      ActualRichLine (representative g) (representative_det_ne_zero g) Q ∧
      ActualOneMatching (representative g) (representative_det_ne_zero g) Q :=
  actualMonochromaticLines_exact _ _ (representative_proportional_faithful g) _ (richDomainLines_exact g) Q

theorem richDomainLines_filter (g : PlatonicModel) (n : ℕ) (hn : 3≤n) :
    (richDomainLines g).filter (fun L => L.card=n)=(domainLines g).filter (fun L => L.card=n) := by
  ext L
  simp only [richDomainLines,Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · intro h
    exact ⟨⟨h.1,by omega⟩,h.2⟩

/-- The exact 6|G| multiplicity, now for the actual projective deck sets. -/
theorem standardMonochromaticLines_filter_card (g : PlatonicModel) (n : ℕ) (hn : 3≤n) :
    ((standardMonochromaticLines g).filter (fun Q => Q.card=n)).card=
      6*size g*((domainLines g).filter (fun L => L.card=n)).card := by
  rw [standardMonochromaticLines,actualMonochromaticLines_filter_card _ _
    (representative_proportional_faithful g) (richDomainLines g) (fun L hL =>
      le_trans (by decide : 2≤3) (Finset.mem_filter.mp hL).2),richDomainLines_filter g n hn]
  simp

theorem tetrahedral_monochromatic_counts :
    ((standardMonochromaticLines .tetrahedral).filter (fun Q => Q.card=3)).card=1152 ∧
    ((standardMonochromaticLines .tetrahedral).filter (fun Q => Q.card=4)).card=0 ∧
    ((standardMonochromaticLines .tetrahedral).filter (fun Q => Q.card=5)).card=0 := by
  rw [standardMonochromaticLines_filter_card _ 3 (by decide),
    standardMonochromaticLines_filter_card _ 4 (by decide),
    standardMonochromaticLines_filter_card _ 5 (by decide),
    tetrahedral_domain_counts.2.1,tetrahedral_domain_counts.2.2.1,tetrahedral_domain_counts.2.2.2]
  norm_num [size]

theorem octahedral_monochromatic_counts :
    ((standardMonochromaticLines .octahedral).filter (fun Q => Q.card=3)).card=4608 ∧
    ((standardMonochromaticLines .octahedral).filter (fun Q => Q.card=4)).card=2592 ∧
    ((standardMonochromaticLines .octahedral).filter (fun Q => Q.card=5)).card=0 := by
  rw [standardMonochromaticLines_filter_card _ 3 (by decide),
    standardMonochromaticLines_filter_card _ 4 (by decide),
    standardMonochromaticLines_filter_card _ 5 (by decide),
    octahedral_domain_counts.2.1,octahedral_domain_counts.2.2.1,octahedral_domain_counts.2.2.2]
  norm_num [size]

theorem icosahedral_monochromatic_counts :
    ((standardMonochromaticLines .icosahedral).filter (fun Q => Q.card=3)).card=72000 ∧
    ((standardMonochromaticLines .icosahedral).filter (fun Q => Q.card=4)).card=0 ∧
    ((standardMonochromaticLines .icosahedral).filter (fun Q => Q.card=5)).card=25920 := by
  rw [standardMonochromaticLines_filter_card _ 3 (by decide),
    standardMonochromaticLines_filter_card _ 4 (by decide),
    standardMonochromaticLines_filter_card _ 5 (by decide),
    icosahedral_domain_counts.2.1,icosahedral_domain_counts.2.2.1,icosahedral_domain_counts.2.2.2]
  norm_num [size]

theorem standard_actual_rich_classification (g : PlatonicModel) (Q : Finset Point)
    (hQ : ActualRichLine (representative g) (representative_det_ne_zero g) Q) :
    Q∈standardMonochromaticLines g ∨ RainbowLine g Q := by
  classical
  rcases actualRichLine_mono_or_rainbow (representative g) (representative_det_ne_zero g)
      (representative_proportional_faithful g) (groupDirection g) (representative_mem g) Q hQ with h|h
  · obtain ⟨r,b,f,L,hL,hc,rfl⟩ := h
    left
    apply Finset.mem_image.mpr
    refine ⟨rulingSet r b f L,?_,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(r,b,f,L),?_,rfl⟩
    have hm := (richDomainLines_exact g L).mpr ⟨hL,hc⟩
    simpa [rulingParameters] using hm
  · exact Or.inr h

theorem standard_monochromatic_card_bounds (g : PlatonicModel) (Q : Finset Point)
    (hQ : Q∈standardMonochromaticLines g) : 3≤Q.card ∧ Q.card≤maximumLineSize g := by
  classical
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨⟨r,b,f,L⟩,hp,rfl⟩ := Finset.mem_image.mp hS
  have hL : L∈richDomainLines g := by simpa [rulingParameters] using hp
  have hc := Finset.mem_filter.mp hL
  simpa only [configurationPoints_card _ _ (representative_proportional_faithful g),
    rulingMap,rulingSet_card] using And.intro hc.2 (domainLines_size_bound g L hc.1).2

theorem standard_monochromatic_sizes (g : PlatonicModel) (Q : Finset Point)
    (hQ : Q∈standardMonochromaticLines g) :
    match g with
    | .tetrahedral => Q.card=3
    | .octahedral => Q.card=3 ∨ Q.card=4
    | .icosahedral => Q.card=3 ∨ Q.card=5 := by
  have hb := standard_monochromatic_card_bounds g Q hQ
  cases g
  · simp only [maximumLineSize] at hb
    omega
  · simp only [maximumLineSize] at hb
    omega
  · simp only [maximumLineSize] at hb
    have hfour : Q.card≠4 := by
      intro hc
      have hm : Q∈(standardMonochromaticLines .icosahedral).filter (fun Q => Q.card=4) :=
        Finset.mem_filter.mpr ⟨hQ,hc⟩
      rw [Finset.card_eq_zero.mp icosahedral_monochromatic_counts.2.1] at hm
      exact Finset.notMem_empty _ hm
    omega

theorem standard_actual_rich_complete_iff (g : PlatonicModel) (Q : Finset Point) :
    ActualRichLine (representative g) (representative_det_ne_zero g) Q ↔
      Q∈standardMonochromaticLines g ∨ RainbowLine g Q := by
  exact actualRichLine_complete_iff (representative g) (representative_det_ne_zero g)
    (representative_proportional_faithful g) (groupDirection g) (representative_mem g)
    (groupDirection_det_ne_zero g)
    (by intro U hU; obtain ⟨i,c,hc,hi⟩ := (complete g U).mp hU; exact ⟨i,c,hc,hi⟩)
    (richDomainLines g) (richDomainLines_exact g) Q

theorem standard_monochromatic_not_rainbow (g : PlatonicModel) (Q : Finset Point)
    (hQ : Q∈standardMonochromaticLines g) : ¬RainbowLine g Q := by
  exact actual_monochromatic_rainbow_disjoint (representative g) (representative_det_ne_zero g)
    (representative_proportional_faithful g) (groupDirection g)
    (by intro U hU; obtain ⟨i,c,hc,hi⟩ := (complete g U).mp hU; exact ⟨i,c,hc,hi⟩)
    (richDomainLines g) (richDomainLines_exact g) Q hQ

/-- Semantic monochromatic count on arbitrary actual complex projective lines. -/
def standardMonochromaticCount (g : PlatonicModel) (n : ℕ) : ℕ :=
  {Q : Finset Point | ActualRichLine (representative g) (representative_det_ne_zero g) Q ∧
    ActualOneMatching (representative g) (representative_det_ne_zero g) Q ∧ Q.card=n}.ncard

theorem standardMonochromaticCount_eq (g : PlatonicModel) (n : ℕ) :
    standardMonochromaticCount g n=
      ((standardMonochromaticLines g).filter (fun Q => Q.card=n)).card := by
  classical
  have he : {Q : Finset Point | ActualRichLine (representative g) (representative_det_ne_zero g) Q ∧
      ActualOneMatching (representative g) (representative_det_ne_zero g) Q ∧ Q.card=n}=
      ((standardMonochromaticLines g).filter (fun Q => Q.card=n) : Set (Finset Point)) := by
    ext Q
    simp only [Finset.mem_coe,Finset.mem_filter,standardMonochromaticLines_exact,
      Set.mem_setOf_eq,and_assoc]
  rw [standardMonochromaticCount,he,Set.ncard_coe_finset]

/-- All nine source monochromatic entries, as counts of semantic actual lines. -/
theorem standard_semantic_monochromatic_counts :
    (standardMonochromaticCount .tetrahedral 3=1152 ∧
      standardMonochromaticCount .tetrahedral 4=0 ∧ standardMonochromaticCount .tetrahedral 5=0) ∧
    (standardMonochromaticCount .octahedral 3=4608 ∧
      standardMonochromaticCount .octahedral 4=2592 ∧ standardMonochromaticCount .octahedral 5=0) ∧
    (standardMonochromaticCount .icosahedral 3=72000 ∧
      standardMonochromaticCount .icosahedral 4=0 ∧ standardMonochromaticCount .icosahedral 5=25920) := by
  simp only [standardMonochromaticCount_eq]
  exact ⟨tetrahedral_monochromatic_counts,octahedral_monochromatic_counts,icosahedral_monochromatic_counts⟩

/-- No unlisted monochromatic line size occurs in any standard deck. -/
theorem standardMonochromaticCount_all (g : PlatonicModel) (n : ℕ) :
    standardMonochromaticCount g n=
      match g with
      | .tetrahedral => if n=3 then 1152 else 0
      | .octahedral => if n=3 then 4608 else if n=4 then 2592 else 0
      | .icosahedral => if n=3 then 72000 else if n=5 then 25920 else 0 := by
  classical
  have hz (g : PlatonicModel)
      (hn : ∀Q∈standardMonochromaticLines g,Q.card≠n) : standardMonochromaticCount g n=0 := by
    rw [standardMonochromaticCount_eq,Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    exact hn
  cases g
  · by_cases h3 : n=3
    · subst n
      simpa using standard_semantic_monochromatic_counts.1.1
    · simp only [h3,↓reduceIte]
      exact hz _ (fun Q hQ hc => h3 (hc.symm.trans (standard_monochromatic_sizes _ Q hQ)))
  · by_cases h3 : n=3
    · subst n
      simpa using standard_semantic_monochromatic_counts.2.1.1
    · by_cases h4 : n=4
      · subst n
        simpa using standard_semantic_monochromatic_counts.2.1.2.1
      · simp only [h3,h4,↓reduceIte]
        apply hz
        intro Q hQ hc
        rcases standard_monochromatic_sizes _ Q hQ with hh|hh
        · exact h3 (hc.symm.trans hh)
        · exact h4 (hc.symm.trans hh)
  · by_cases h3 : n=3
    · subst n
      simpa using standard_semantic_monochromatic_counts.2.2.1
    · by_cases h5 : n=5
      · subst n
        simpa using standard_semantic_monochromatic_counts.2.2.2.2
      · simp only [h3,h5,↓reduceIte]
        apply hz
        intro Q hQ hc
        rcases standard_monochromatic_sizes _ Q hQ with hh|hh
        · exact h3 (hc.symm.trans hh)
        · exact h5 (hc.symm.trans hh)

end
end Holant.Certificates.PlatonicIncidence
