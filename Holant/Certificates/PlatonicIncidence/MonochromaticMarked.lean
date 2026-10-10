import Holant.Certificates.PlatonicIncidence.MonochromaticStandard
import Holant.Certificates.PlatonicIncidence.MonochromaticTransport
import Holant.Certificates.PlatonicIncidence.MonochromaticMaximal

namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

def externalMonochromaticLines : Finset (Finset Point) :=
  actualMonochromaticLines External.representative External.representative_det_ne_zero (richDomainLines .tetrahedral)

def markedMonochromaticLines (f : Form) : Finset (Finset Point) :=
  actualMonochromaticLines (markedRepresentative f) (markedRepresentative_det f) (richDomainLines .octahedral)

theorem external_richDomainLines_exact (L : Finset (Fin 12)) :
    L∈richDomainLines .tetrahedral ↔ BinarySecant External.representative L ∧ 3≤L.card := by
  rw [richDomainLines_exact,external_binarySecant_iff]

theorem marked_richDomainLines_exact (f : Form) (L : Finset (Fin 24)) :
    L∈richDomainLines .octahedral ↔ BinarySecant (markedRepresentative f) L ∧ 3≤L.card := by
  rw [richDomainLines_exact,marked_binarySecant_iff]

theorem externalMonochromaticLines_exact (Q : Finset Point) :
    Q∈externalMonochromaticLines ↔
      ActualRichLine External.representative External.representative_det_ne_zero Q ∧
      ActualOneMatching External.representative External.representative_det_ne_zero Q :=
  actualMonochromaticLines_exact _ _ external_representative_faithful _ external_richDomainLines_exact Q

theorem markedMonochromaticLines_exact (f : Form) (Q : Finset Point) :
    Q∈markedMonochromaticLines f ↔
      ActualRichLine (markedRepresentative f) (markedRepresentative_det f) Q ∧
      ActualOneMatching (markedRepresentative f) (markedRepresentative_det f) Q :=
  actualMonochromaticLines_exact _ _ (marked_representative_faithful f) _ (marked_richDomainLines_exact f) Q

theorem externalMonochromaticLines_filter_card (n : ℕ) :
    ((externalMonochromaticLines).filter (fun Q => Q.card=n)).card=
      ((standardMonochromaticLines .tetrahedral).filter (fun Q => Q.card=n)).card := by
  rw [externalMonochromaticLines,standardMonochromaticLines,
    actualMonochromaticLines_filter_card _ _ external_representative_faithful (richDomainLines .tetrahedral)
      (fun L hL => le_trans (by decide : 2≤3) (Finset.mem_filter.mp hL).2),
    actualMonochromaticLines_filter_card _ _ (representative_proportional_faithful .tetrahedral) (richDomainLines .tetrahedral)
      (fun L hL => le_trans (by decide : 2≤3) (Finset.mem_filter.mp hL).2)]
  simp only [Fintype.card_fin,size]

theorem markedMonochromaticLines_filter_card (f : Form) (n : ℕ) :
    ((markedMonochromaticLines f).filter (fun Q => Q.card=n)).card=
      ((standardMonochromaticLines .octahedral).filter (fun Q => Q.card=n)).card := by
  rw [markedMonochromaticLines,standardMonochromaticLines,
    actualMonochromaticLines_filter_card _ _ (marked_representative_faithful f) (richDomainLines .octahedral)
      (fun L hL => le_trans (by decide : 2≤3) (Finset.mem_filter.mp hL).2),
    actualMonochromaticLines_filter_card _ _ (representative_proportional_faithful .octahedral) (richDomainLines .octahedral)
      (fun L hL => le_trans (by decide : 2≤3) (Finset.mem_filter.mp hL).2)]
  simp only [Fintype.card_fin,size]

theorem external_monochromatic_counts :
    ((externalMonochromaticLines).filter (fun Q => Q.card=3)).card=1152 ∧
    ((externalMonochromaticLines).filter (fun Q => Q.card=4)).card=0 ∧
    ((externalMonochromaticLines).filter (fun Q => Q.card=5)).card=0 := by
  simpa only [externalMonochromaticLines_filter_card] using tetrahedral_monochromatic_counts

theorem marked_monochromatic_counts (f : Form) :
    ((markedMonochromaticLines f).filter (fun Q => Q.card=3)).card=4608 ∧
    ((markedMonochromaticLines f).filter (fun Q => Q.card=4)).card=2592 ∧
    ((markedMonochromaticLines f).filter (fun Q => Q.card=5)).card=0 := by
  simpa only [markedMonochromaticLines_filter_card] using octahedral_monochromatic_counts

/-- The external deck has only complete monochromatic three-line rulings. -/
theorem external_actual_rich_classification (Q : Finset Point)
    (hQ : ActualRichLine External.representative External.representative_det_ne_zero Q) :
    Q∈externalMonochromaticLines := by
  classical
  rcases actualRichLine_mono_or_rainbow External.representative External.representative_det_ne_zero
      external_representative_faithful External.Direction External.Direction.representative Q hQ with h|h
  · obtain ⟨r,b,f,L,hL,hc,rfl⟩ := h
    apply Finset.mem_image.mpr
    refine ⟨rulingSet r b f L,?_,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(r,b,f,L),?_,rfl⟩
    have hm := (external_richDomainLines_exact L).mpr ⟨hL,hc⟩
    simpa [rulingParameters] using hm
  · obtain ⟨p,hp,_⟩ := h
    exact False.elim (External.no_rainbow p hp)

theorem marked_actual_rich_classification (f : Form) (Q : Finset Point)
    (hQ : ActualRichLine (markedRepresentative f) (markedRepresentative_det f) Q) :
    Q∈markedMonochromaticLines f ∨ MarkedRainbowLine f Q := by
  classical
  rcases actualRichLine_mono_or_rainbow (markedRepresentative f) (markedRepresentative_det f)
      (marked_representative_faithful f) (Direction f) (Direction.standard f) Q hQ with h|h
  · obtain ⟨r,b,k,L,hL,hc,rfl⟩ := h
    left
    apply Finset.mem_image.mpr
    refine ⟨rulingSet r b k L,?_,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(r,b,k,L),?_,rfl⟩
    have hm := (marked_richDomainLines_exact f L).mpr ⟨hL,hc⟩
    simpa [rulingParameters] using hm
  · exact Or.inr h

theorem standard_configurationDeck (g : PlatonicModel) :
    configurationPoints (representative g) (representative_det_ne_zero g) Finset.univ=deck g := by
  classical
  simp only [configurationPoints,deck,Finset.map_eq_image]
  rfl

theorem external_configurationDeck :
    configurationPoints External.representative External.representative_det_ne_zero Finset.univ=External.deck := by
  classical
  simp only [configurationPoints,External.deck,Finset.map_eq_image]
  rfl

theorem marked_configurationDeck (f : Form) :
    configurationPoints (markedRepresentative f) (markedRepresentative_det f) Finset.univ=markedDeck f := by
  classical
  ext q
  rw [configurationDeck_iff_familyDeckPoint (markedRepresentative f) (markedRepresentative_det f) (Direction f) (Direction.standard f)
    (by intro U hU; obtain ⟨c,hc,i,hi⟩ := hU; exact ⟨i,c,hc,hi⟩),←markedDeck_iff_mem]
  rfl

theorem external_actual_rich_complete_iff (Q : Finset Point) :
    ActualRichLine External.representative External.representative_det_ne_zero Q ↔
      Q∈externalMonochromaticLines :=
  ⟨external_actual_rich_classification Q,fun h => (externalMonochromaticLines_exact Q).mp h |>.1⟩

theorem marked_actual_rich_complete_iff (f : Form) (Q : Finset Point) :
    ActualRichLine (markedRepresentative f) (markedRepresentative_det f) Q ↔
      Q∈markedMonochromaticLines f ∨ MarkedRainbowLine f Q := by
  exact actualRichLine_complete_iff (markedRepresentative f) (markedRepresentative_det f)
    (marked_representative_faithful f) (Direction f) (Direction.standard f)
    Direction.det_ne_zero
    (by intro U hU; obtain ⟨c,hc,i,hi⟩ := hU; exact ⟨i,c,hc,hi⟩)
    (richDomainLines .octahedral) (marked_richDomainLines_exact f) Q

theorem external_monochromatic_size (Q : Finset Point) (hQ : Q∈externalMonochromaticLines) : Q.card=3 := by
  classical
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hQ
  have hm : configurationPoints (representative .tetrahedral) (representative_det_ne_zero .tetrahedral) S∈
      standardMonochromaticLines .tetrahedral := Finset.mem_image.mpr ⟨S,hS,rfl⟩
  have hc := standard_monochromatic_sizes .tetrahedral _ hm
  rw [configurationPoints_card _ _ external_representative_faithful]
  simpa only [configurationPoints_card _ _ (representative_proportional_faithful .tetrahedral)] using hc

theorem marked_monochromatic_sizes (f : Form) (Q : Finset Point)
    (hQ : Q∈markedMonochromaticLines f) : Q.card=3 ∨ Q.card=4 := by
  classical
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hQ
  have hm : configurationPoints (representative .octahedral) (representative_det_ne_zero .octahedral) S∈
      standardMonochromaticLines .octahedral := Finset.mem_image.mpr ⟨S,hS,rfl⟩
  have hc := standard_monochromatic_sizes .octahedral _ hm
  rw [configurationPoints_card _ _ (marked_representative_faithful f)]
  simpa only [configurationPoints_card _ _ (representative_proportional_faithful .octahedral)] using hc

def externalMonochromaticCount (n : ℕ) : ℕ :=
  {Q : Finset Point | ActualRichLine External.representative External.representative_det_ne_zero Q ∧
    ActualOneMatching External.representative External.representative_det_ne_zero Q ∧ Q.card=n}.ncard

def markedMonochromaticCount (f : Form) (n : ℕ) : ℕ :=
  {Q : Finset Point | ActualRichLine (markedRepresentative f) (markedRepresentative_det f) Q ∧
    ActualOneMatching (markedRepresentative f) (markedRepresentative_det f) Q ∧ Q.card=n}.ncard

theorem externalMonochromaticCount_eq (n : ℕ) :
    externalMonochromaticCount n=standardMonochromaticCount .tetrahedral n := by
  rw [externalMonochromaticCount,standardMonochromaticCount,
    actual_monochromatic_ncard _ _ external_representative_faithful _ external_richDomainLines_exact,
    actual_monochromatic_ncard _ _ (representative_proportional_faithful .tetrahedral) _ (richDomainLines_exact .tetrahedral)]
  simp only [Fintype.card_fin,size]

theorem markedMonochromaticCount_eq (f : Form) (n : ℕ) :
    markedMonochromaticCount f n=standardMonochromaticCount .octahedral n := by
  rw [markedMonochromaticCount,standardMonochromaticCount,
    actual_monochromatic_ncard _ _ (marked_representative_faithful f) _ (marked_richDomainLines_exact f),
    actual_monochromatic_ncard _ _ (representative_proportional_faithful .octahedral) _ (richDomainLines_exact .octahedral)]
  simp only [Fintype.card_fin,size]

theorem external_semantic_monochromatic_counts :
    externalMonochromaticCount 3=1152 ∧ externalMonochromaticCount 4=0 ∧ externalMonochromaticCount 5=0 := by
  simpa only [externalMonochromaticCount_eq] using standard_semantic_monochromatic_counts.1

theorem marked_semantic_monochromatic_counts (f : Form) :
    markedMonochromaticCount f 3=4608 ∧ markedMonochromaticCount f 4=2592 ∧ markedMonochromaticCount f 5=0 := by
  simpa only [markedMonochromaticCount_eq] using standard_semantic_monochromatic_counts.2.1

theorem externalMonochromaticCount_all (n : ℕ) :
    externalMonochromaticCount n=if n=3 then 1152 else 0 := by
  rw [externalMonochromaticCount_eq,standardMonochromaticCount_all]

theorem markedMonochromaticCount_all (f : Form) (n : ℕ) :
    markedMonochromaticCount f n=if n=3 then 4608 else if n=4 then 2592 else 0 := by
  rw [markedMonochromaticCount_eq,standardMonochromaticCount_all]

end
end Holant.Certificates.PlatonicIncidence
