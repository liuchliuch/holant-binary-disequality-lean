import Holant.Certificates.PlatonicIncidence.DomainCounts
import Mathlib.Data.Set.Card

/-! A.19: all actual complex subspace deletions, including their realization.
The source counts are counts of distinct intersections, not just upper bounds. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false

@[simp] theorem deletion_bot (g : PlatonicModel) : deletion g ⊥=∅ := by
  classical
  ext i
  simp [representative_ne_zero]

@[simp] theorem deletion_singleton_span (g : PlatonicModel) (i : Fin (size g)) :
    deletion g (Submodule.span ℂ ({representative g i} : Set Mat))={i} := by
  classical
  ext j
  simp only [mem_deletion,Finset.mem_singleton]
  constructor
  · intro h
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
    exact projectively_injective g j i c hc.symm
  · rintro rfl
    exact Submodule.mem_span_singleton_self _

/-- The empty deletion, each singleton, and each actual two-point span. -/
def deletionSets (g : PlatonicModel) : Finset (Finset (Fin (size g))) :=
  insert ∅ ((Finset.univ.image (fun i : Fin (size g) => {i})) ∪ domainLines g)

theorem deletionSets_exact (g : PlatonicModel) (S : Finset (Fin (size g))) :
    S∈deletionSets g ↔ ∃W : Submodule ℂ Mat,Module.finrank ℂ W≤2 ∧ deletion g W=S := by
  classical
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with rfl|h
    · exact ⟨⊥,by simp, deletion_bot g⟩
    rcases Finset.mem_union.mp h with h|h
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact ⟨Submodule.span ℂ ({representative g i} : Set Mat),
        by rw [finrank_span_singleton (representative_ne_zero g i)]; decide,deletion_singleton_span g i⟩
    · obtain ⟨i,j,hij,hS⟩ := (domainLines_exact g S).mp h
      exact ⟨Submodule.span ℂ ({representative g i,representative g j} : Set Mat),
        by rw [pair_finrank g i j hij],Finset.ext (fun k => (mem_deletion _ _ _).trans (hS k).symm)⟩
  · rintro ⟨W,hW,rfl⟩
    rcases deletion_classification g W hW with h|⟨t,ht⟩
    · by_cases he : deletion g W=∅
      · simp [he,deletionSets]
      · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr he
        have hs : deletion g W={i} := by
          ext j
          constructor
          · intro hj
            exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp h) j hj i hi)
          · intro hj
            simpa only [Finset.mem_singleton.mp hj] using hi
        simp [deletionSets,hs]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_union_right
      rw [ht]
      exact Finset.mem_map.mpr ⟨t,Finset.mem_univ t,rfl⟩

theorem deletionSets_card (g : PlatonicModel) :
    (deletionSets g).card=1+size g+secantCount g := by
  classical
  have hdis : Disjoint (Finset.univ.image (fun i : Fin (size g) => ({i} : Finset _))) (domainLines g) := by
    apply Finset.disjoint_left.mpr
    intro S hS hL
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
    have h := (domainLines_size_bound g {i} hL).1
    simpa using h
  have hempty : (∅ : Finset (Fin (size g)))∉
      (Finset.univ.image (fun i : Fin (size g) => {i})) ∪ domainLines g := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · simpa using h
    · have hh := (domainLines_size_bound g ∅ h).1
      simpa using hh
  rw [deletionSets,Finset.card_insert_of_notMem hempty,Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_injective h),domainLines_card]
  simp only [Finset.card_univ,Fintype.card_fin]
  omega

/-- Semantic count of all distinct intersections with every complex subspace
of dimension at most two. -/
theorem actual_deletion_count (g : PlatonicModel) :
    {S : Finset (Fin (size g)) | ∃W : Submodule ℂ Mat,
      Module.finrank ℂ W≤2 ∧ deletion g W=S}.ncard=1+size g+secantCount g := by
  have he : {S : Finset (Fin (size g)) | ∃W : Submodule ℂ Mat,
      Module.finrank ℂ W≤2 ∧ deletion g W=S}=(deletionSets g : Set _) := by
    ext S
    exact (deletionSets_exact g S).symm
  rw [he,Set.ncard_coe_finset,deletionSets_card]

theorem source_deletion_counts :
    (deletionSets .tetrahedral).card=47 ∧ (deletionSets .octahedral).card=147 ∧
    (deletionSets .icosahedral).card=783 := by
  exact ⟨deletionSets_card .tetrahedral,deletionSets_card .octahedral,
    deletionSets_card .icosahedral⟩

end
end Holant.Certificates.PlatonicAtlas
