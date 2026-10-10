import Holant.Certificates.PlatonicAtlas.MonochromaticIncidences
import Holant.Certificates.PlatonicAtlas.RainbowIncidences
import Holant.Certificates.PlatonicIncidence.MonochromaticExclusions

namespace Holant.Certificates.PlatonicAtlas
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
local instance richIncidenceCountsPointDecidable : DecidableEq Point := Classical.decEq _

 theorem basePoint_zero_eq_deck (g : PlatonicModel) :
    basePoint 0=deckPoint g (0,identityIndex g,identityIndex g) := by
  apply (proportional_point_iff _ _ _ _).mp
  change Proportional A (matchingTensor 0 (representative g (identityIndex g)) (representative g (identityIndex g)))
  rw [representative_identity,A_matrix]
  exact Proportional.refl _

 theorem standard_rich_families_disjoint (g : PlatonicModel) :
    Disjoint (standardMonochromaticLines g) (lines g) := by
  apply Finset.disjoint_left.mpr
  intro Q hQ hR
  exact familyRainbowLine_not_one_matching (representative g) (representative_det_ne_zero g)
    (groupDirection g) (fun U hU => (complete g U).mp hU) Q
    ((rainbowLine_iff_mem g Q).mpr hR) ((standardMonochromaticLines_exact g Q).mp hQ).2

 theorem rainbow_at_base_card (g : PlatonicModel) (n : ℕ) :
    ((lines g).filter (fun Q => basePoint 0∈Q ∧ Q.card=n)).card=
      if n=3 then size g else 0 := by
  by_cases hn : n=3
  · subst n
    have he : (lines g).filter (fun Q => basePoint 0∈Q ∧ Q.card=3)=
        (lines g).filter (fun Q => basePoint 0∈Q) := by
      ext Q
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1,h.2.1⟩
      · exact fun h => ⟨h.1,h.2,rainbowLine_three ((rainbowLine_iff_mem g Q).mpr h.1)⟩
    rw [he,rainbow_lines_through_base,if_pos rfl]
  · rw [if_neg hn]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro Q hQ
    have h3 := rainbowLine_three ((rainbowLine_iff_mem g Q).mpr (Finset.mem_filter.mp hQ).1)
    exact hn ((Finset.mem_filter.mp hQ).2.2.symm.trans h3)

 theorem standard_actual_rich_incidences (g : PlatonicModel) (n : ℕ) (hn : 3≤n) :
    {Q : Finset Point | ActualRichLine (representative g) (representative_det_ne_zero g) Q ∧
      basePoint 0∈Q ∧ Q.card=n}.ncard=
      2*(linesThrough g (identityIndex g) n).card+(if n=3 then size g else 0) := by
  have he : {Q : Finset Point | ActualRichLine (representative g) (representative_det_ne_zero g) Q ∧
      basePoint 0∈Q ∧ Q.card=n}=
      (((standardMonochromaticLines g∪lines g).filter (fun Q => basePoint 0∈Q ∧ Q.card=n)) : Set _) := by
    ext Q
    simp only [Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_filter,Finset.mem_union,
      standard_actual_rich_complete_iff,rainbowLine_iff_mem]
  rw [he,Set.ncard_coe_finset,Finset.filter_union,Finset.card_union_of_disjoint
    ((standard_rich_families_disjoint g).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    rainbow_at_base_card,basePoint_zero_eq_deck]
  rw [standard_monochromatic_incidences g 0 (identityIndex g) n hn]

 theorem external_actual_rich_incidences :
    {Q : Finset Point | ActualRichLine External.representative External.representative_det_ne_zero Q ∧
      External.deckPoint (0,0,0)∈Q ∧ Q.card=3}.ncard=8 := by
  have he : {Q : Finset Point | ActualRichLine External.representative External.representative_det_ne_zero Q ∧
      External.deckPoint (0,0,0)∈Q ∧ Q.card=3}=
      ((externalMonochromaticLines.filter (fun Q => External.deckPoint (0,0,0)∈Q ∧ Q.card=3)) : Set _) := by
    ext Q
    simp only [Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_filter,external_actual_rich_complete_iff]
  rw [he,Set.ncard_coe_finset]
  exact external_monochromatic_incidences 0 0

 theorem source_rich_point_incidences :
    {Q : Finset Point | ActualRichLine (representative .octahedral) (representative_det_ne_zero .octahedral) Q ∧
      basePoint 0∈Q ∧ Q.card=3}.ncard=32 ∧
    {Q : Finset Point | ActualRichLine (representative .octahedral) (representative_det_ne_zero .octahedral) Q ∧
      basePoint 0∈Q ∧ Q.card=4}.ncard=6 ∧
    {Q : Finset Point | ActualRichLine (representative .icosahedral) (representative_det_ne_zero .icosahedral) Q ∧
      basePoint 0∈Q ∧ Q.card=3}.ncard=80 ∧
    {Q : Finset Point | ActualRichLine (representative .icosahedral) (representative_det_ne_zero .icosahedral) Q ∧
      basePoint 0∈Q ∧ Q.card=5}.ncard=12 := by
  rw [standard_actual_rich_incidences _ 3 (by decide),standard_actual_rich_incidences _ 4 (by decide),
    standard_actual_rich_incidences _ 3 (by decide),standard_actual_rich_incidences _ 5 (by decide),
    (octahedral_point_incidences _).1,(octahedral_point_incidences _).2,
    (icosahedral_point_incidences _).1,(icosahedral_point_incidences _).2]
  decide

end
end Holant.Certificates.PlatonicAtlas
