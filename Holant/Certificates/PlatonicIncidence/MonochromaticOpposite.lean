import Holant.Certificates.PlatonicIncidence.MonochromaticStandard
import Holant.Certificates.PlatonicIncidence.CoefficientEquivs
import Holant.Certificates.PlatonicIncidence.OppositeOrbit

/-! The monochromatic classification and counts in the literal opposite-I
representatives. The coefficient similarity is used only as a domain incidence
dictionary; current-group physical rainbow witnesses remain separate. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OppositeIcosahedral
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

theorem opposite_representative_faithful (i j : Fin 60)
    (h : Proportional (oppositeRepresentative i) (oppositeRepresentative j)) : i=j := by
  obtain ⟨c,_,hc⟩ := h
  exact oppositeRepresentative_projectively_injective i j c hc

theorem opposite_binarySecant_iff (L : Finset (Fin 60)) :
    BinarySecant oppositeRepresentative L ↔ BinarySecant (representative .icosahedral) L := by
  have he : oppositeRepresentative=(fun i => oppositeEquiv (representative .icosahedral i)) := by
    funext i
    exact (opposite_dictionary i).symm
  rw [he]
  exact binarySecant_linearEquiv_iff _ _ _

theorem opposite_richDomainLines_exact (L : Finset (Fin 60)) :
    L∈richDomainLines .icosahedral ↔ BinarySecant oppositeRepresentative L ∧ 3≤L.card := by
  rw [richDomainLines_exact,opposite_binarySecant_iff]

def oppositeMonochromaticLines : Finset (Finset Point) :=
  actualMonochromaticLines oppositeRepresentative oppositeRepresentative_det (richDomainLines .icosahedral)

theorem oppositeMonochromaticLines_exact (Q : Finset Point) :
    Q∈oppositeMonochromaticLines ↔
      ActualRichLine oppositeRepresentative oppositeRepresentative_det Q ∧
      ActualOneMatching oppositeRepresentative oppositeRepresentative_det Q :=
  actualMonochromaticLines_exact _ _ opposite_representative_faithful _ opposite_richDomainLines_exact Q

theorem oppositeMonochromaticLines_filter_card (n : ℕ) :
    ((oppositeMonochromaticLines).filter (fun Q => Q.card=n)).card=
      ((standardMonochromaticLines .icosahedral).filter (fun Q => Q.card=n)).card := by
  rw [oppositeMonochromaticLines,standardMonochromaticLines,
    actualMonochromaticLines_filter_card _ _ opposite_representative_faithful (richDomainLines .icosahedral)
      (fun L hL => le_trans (by decide : 2≤3) (Finset.mem_filter.mp hL).2),
    actualMonochromaticLines_filter_card _ _ (representative_proportional_faithful .icosahedral) (richDomainLines .icosahedral)
      (fun L hL => le_trans (by decide : 2≤3) (Finset.mem_filter.mp hL).2)]
  simp only [Fintype.card_fin,size]

theorem opposite_monochromatic_counts :
    ((oppositeMonochromaticLines).filter (fun Q => Q.card=3)).card=72000 ∧
    ((oppositeMonochromaticLines).filter (fun Q => Q.card=4)).card=0 ∧
    ((oppositeMonochromaticLines).filter (fun Q => Q.card=5)).card=25920 := by
  simpa only [oppositeMonochromaticLines_filter_card] using icosahedral_monochromatic_counts

theorem opposite_actual_rich_complete_iff (Q : Finset Point) :
    ActualRichLine oppositeRepresentative oppositeRepresentative_det Q ↔
      Q∈oppositeMonochromaticLines ∨ Opposite.RainbowLine Q := by
  exact actualRichLine_complete_iff oppositeRepresentative oppositeRepresentative_det
    opposite_representative_faithful Direction oppositeRepresentative_mem Direction.det_ne_zero
    (by intro U hU; obtain ⟨i,c,hc,hi⟩ := (direction_complete U).mp hU; exact ⟨i,c,hc,hi⟩)
    (richDomainLines .icosahedral) opposite_richDomainLines_exact Q

theorem opposite_monochromatic_sizes (Q : Finset Point)
    (hQ : Q∈oppositeMonochromaticLines) : Q.card=3 ∨ Q.card=5 := by
  classical
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hQ
  have hm : configurationPoints (representative .icosahedral) (representative_det_ne_zero .icosahedral) S∈
      standardMonochromaticLines .icosahedral := Finset.mem_image.mpr ⟨S,hS,rfl⟩
  have hc := standard_monochromatic_sizes .icosahedral _ hm
  rw [configurationPoints_card _ _ opposite_representative_faithful]
  simpa only [configurationPoints_card _ _ (representative_proportional_faithful .icosahedral)] using hc

theorem opposite_configurationDeck :
    configurationPoints oppositeRepresentative oppositeRepresentative_det Finset.univ=Opposite.deck := by
  classical
  ext q
  rw [configurationDeck_iff_familyDeckPoint _ _ Direction oppositeRepresentative_mem
    (by intro U hU; obtain ⟨i,c,hc,hi⟩ := (direction_complete U).mp hU; exact ⟨i,c,hc,hi⟩),←Opposite.deck_iff_mem]
  rfl

def oppositeMonochromaticCount (n : ℕ) : ℕ :=
  {Q : Finset Point | ActualRichLine oppositeRepresentative oppositeRepresentative_det Q ∧
    ActualOneMatching oppositeRepresentative oppositeRepresentative_det Q ∧ Q.card=n}.ncard

theorem oppositeMonochromaticCount_eq (n : ℕ) :
    oppositeMonochromaticCount n=standardMonochromaticCount .icosahedral n := by
  rw [oppositeMonochromaticCount,standardMonochromaticCount,
    actual_monochromatic_ncard _ _ opposite_representative_faithful _ opposite_richDomainLines_exact,
    actual_monochromatic_ncard _ _ (representative_proportional_faithful .icosahedral) _ (richDomainLines_exact .icosahedral)]
  simp only [Fintype.card_fin,size]

theorem opposite_semantic_monochromatic_counts :
    oppositeMonochromaticCount 3=72000 ∧ oppositeMonochromaticCount 4=0 ∧ oppositeMonochromaticCount 5=25920 := by
  simpa only [oppositeMonochromaticCount_eq] using standard_semantic_monochromatic_counts.2.2

/-- The complete opposite-I A.20 row, with source-level semantic line counts. -/
theorem opposite_complete_deck_counts :
    {Q : Finset Point | Opposite.RainbowLine Q}.ncard=216000 ∧
    oppositeMonochromaticCount 3=72000 ∧ oppositeMonochromaticCount 4=0 ∧ oppositeMonochromaticCount 5=25920 :=
  ⟨Opposite.all_rainbow_lines_card,opposite_semantic_monochromatic_counts⟩

theorem oppositeMonochromaticCount_all (n : ℕ) :
    oppositeMonochromaticCount n=if n=3 then 72000 else if n=5 then 25920 else 0 := by
  rw [oppositeMonochromaticCount_eq,standardMonochromaticCount_all]

end
end Holant.Certificates.PlatonicIncidence
