import Holant.Certificates.PlatonicIncidence.DomainGraph
import Holant.Certificates.PlatonicIncidence.DomainCounts

/-! A.19 point incidences from the genuine left multiplication permutation.
Only the 7/13/31 identity secants are counted by kernel computation. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem baseLine_injective (g : PlatonicModel) : Function.Injective (baseLine g) := by
  cases g <;> decide +kernel

theorem translatedLine_card (g : PlatonicModel) (i : Fin (size g)) (b : Fin (baseCount g)) :
    (translatedLine g i b).card=(baseLine g b).card :=
  Finset.card_image_of_injective _ (left_product_injective g i)

theorem translateIndex_injective (g : PlatonicModel) (i : Fin (size g)) :
    Function.Injective (translateIndex g i) := by
  intro a b hab
  apply baseLine_injective g
  have hh : translatedLine g i a=translatedLine g i b := by
    rw [translation_certificate,translation_certificate,hab]
  apply Finset.image_injective (left_product_injective g i)
  exact hh

theorem self_mem_translatedLine (g : PlatonicModel) (i : Fin (size g)) (b : Fin (baseCount g)) :
    i∈translatedLine g i b := by
  simpa only [product_identity_right] using
    (mem_translated_product g i (identityIndex g) b).mpr (base_anchors g b).2.2.1

theorem line_through_eq_translated (g : PlatonicModel) (i : Fin (size g))
    (t : Fin (secantCount g)) (hi : i∈globalLine g t) :
    ∃b : Fin (baseCount g),translateIndex g i b=t := by
  classical
  obtain ⟨j,hj,hij⟩ : ∃j,j∈globalLine g t ∧ i≠j := by
    by_contra h
    have hs : globalLine g t⊆{i} := by
      intro j hj
      simp only [Finset.mem_singleton]
      by_contra he
      exact h ⟨j,hj,Ne.symm he⟩
    have hc := Finset.card_le_card hs
    have hb := (globalLine_bound g t).1
    simp only [Finset.card_singleton] at hc
    omega
  obtain ⟨b,hb⟩ := secant_complete g i j hij
  have hit : i∈globalLine g (translateIndex g i b) := by
    rw [←translation_certificate,hb]
    exact Submodule.subset_span (by simp)
  have hjt : j∈globalLine g (translateIndex g i b) := by
    rw [←translation_certificate,hb]
    exact Submodule.subset_span (by simp)
  exact ⟨b,((line_pair_certificate g _ i j hit hjt).resolve_left hij).symm.trans
    ((line_pair_certificate g t i j hi hj).resolve_left hij)⟩

/-- Actual secants of specified size through the original source point. -/
def linesThrough (g : PlatonicModel) (i : Fin (size g)) (n : ℕ) :
    Finset (Fin (secantCount g)) :=
  Finset.univ.filter fun t => i∈globalLine g t ∧ (globalLine g t).card=n

theorem linesThrough_eq (g : PlatonicModel) (i : Fin (size g)) (n : ℕ) :
    linesThrough g i n=(Finset.univ.filter (fun b => (baseLine g b).card=n)).image
      (translateIndex g i) := by
  classical
  ext t
  simp only [linesThrough,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨hi,hc⟩
    obtain ⟨b,rfl⟩ := line_through_eq_translated g i t hi
    refine ⟨b,?_,rfl⟩
    rwa [←translation_certificate,translatedLine_card] at hc
  · rintro ⟨b,hb,rfl⟩
    rw [←translation_certificate]
    exact ⟨self_mem_translatedLine g i b,by rw [translatedLine_card]; exact hb⟩

theorem linesThrough_card (g : PlatonicModel) (i : Fin (size g)) (n : ℕ) :
    (linesThrough g i n).card=
      (Finset.univ.filter (fun b : Fin (baseCount g) => (baseLine g b).card=n)).card := by
  rw [linesThrough_eq,Finset.card_image_of_injective _ (translateIndex_injective g i)]

theorem tetrahedral_point_incidences (i : Fin 12) :
    (linesThrough .tetrahedral i 3).card=4 := by
  rw [linesThrough_card]
  decide +kernel

theorem octahedral_point_incidences (i : Fin 24) :
    (linesThrough .octahedral i 3).card=4 ∧ (linesThrough .octahedral i 4).card=3 := by
  simp only [linesThrough_card]
  decide +kernel

theorem icosahedral_point_incidences (i : Fin 60) :
    (linesThrough .icosahedral i 3).card=10 ∧ (linesThrough .icosahedral i 5).card=6 := by
  simp only [linesThrough_card]
  decide +kernel

/-- Remove finite table indices from the incidence cardinal. -/
theorem actual_linesThrough_card (g : PlatonicModel) (i : Fin (size g)) (n : ℕ) :
    {S : Finset (Fin (size g)) | DomainSecant g S ∧ i∈S ∧ S.card=n}.ncard=
      (linesThrough g i n).card := by
  classical
  have he : {S : Finset (Fin (size g)) | DomainSecant g S ∧ i∈S ∧ S.card=n}=
      ((linesThrough g i n).image (globalLine g) : Set _) := by
    ext S
    simp only [Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_image]
    constructor
    · rintro ⟨hS,hi,hc⟩
      obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp ((domainLines_exact g S).mpr hS)
      exact ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ t,hi,hc⟩,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨globalLine_semantics g t,by simpa [linesThrough] using ht⟩
  rw [he,Set.ncard_coe_finset,Finset.card_image_of_injective _ (globalLine_injective g)]

end
end Holant.Certificates.PlatonicAtlas
