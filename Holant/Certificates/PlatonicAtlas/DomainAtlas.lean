import Holant.Certificates.PlatonicAtlas.Deletions
import Holant.Certificates.PlatonicIncidence.ProjectiveDomainGraph

/-! A.19 semantic domain cardinalities and all realized transformed deletions. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def domainPoints (g : PlatonicModel) : Finset DomainPoint :=
  Finset.univ.map ⟨domainPoint g,domainPoint_injective g⟩

 theorem domainPoints_card (g : PlatonicModel) : (domainPoints g).card=size g := by
  simp [domainPoints]

 theorem transformed_domain_points_card (g : PlatonicModel) (e : Mat ≃ₗ[ℂ] Mat) :
    (projectiveDictionary (fun i => e (representative g i))
      (transformed_representative_nonzero g e)).card=size g := by
  classical
  rw [projectiveDictionary,Finset.card_image_of_injective _
    (matrixPoint_injective _ _ (transformed_representative_faithful g e))]
  simp

 theorem external_domain_points_card :
    (projectiveDictionary External.representative External.representative_ne_zero).card=12 := by
  classical
  rw [projectiveDictionary,Finset.card_image_of_injective _
    (matrixPoint_injective _ _ External.projectively_injective)]
  simp

 theorem actual_domain_line_count (g : PlatonicModel) (n : ℕ) :
    {S : Finset (Fin (size g)) | DomainSecant g S ∧ S.card=n}.ncard=
      ((domainLines g).filter (fun S => S.card=n)).card := by
  classical
  have he : {S : Finset (Fin (size g)) | DomainSecant g S ∧ S.card=n}=
      (((domainLines g).filter (fun S => S.card=n)) : Set _) := by
    ext S
    simp only [Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_filter,domainLines_exact]
  rw [he,Set.ncard_coe_finset]

 theorem transformed_deletionSets_exact (g : PlatonicModel) (e : Mat ≃ₗ[ℂ] Mat)
    (S : Finset (Fin (size g))) : S∈deletionSets g ↔
      ∃W : Submodule ℂ Mat,Module.finrank ℂ W≤2 ∧ ∀i : Fin (size g),
        i∈S ↔ e (representative g i)∈W := by
  constructor
  · intro h
    obtain ⟨W,hW,hS⟩ := (deletionSets_exact g S).mp h
    refine ⟨W.map e.toLinearMap,by rw [e.finrank_map_eq]; exact hW,?_⟩
    intro i
    rw [←hS,mem_deletion]
    constructor
    · intro hi
      exact Submodule.mem_map.mpr ⟨representative g i,hi,rfl⟩
    · rintro ⟨v,hv,he⟩
      exact e.injective he ▸ hv
  · rintro ⟨W,hW,hS⟩
    apply (deletionSets_exact g S).mpr
    refine ⟨W.comap e.toLinearMap,?_,?_⟩
    · rw [(e.ofSubmodule' W).finrank_eq]
      exact hW
    · ext i
      exact (mem_deletion _ _ _).trans (hS i).symm

/-- The exact 47/147/783 possible deletion intersections persist under every
actual invertible analytic coefficient dictionary, including all source marks. -/
 theorem transformed_deletion_count (g : PlatonicModel) (e : Mat ≃ₗ[ℂ] Mat) :
    {S : Finset (Fin (size g)) | ∃W : Submodule ℂ Mat,Module.finrank ℂ W≤2 ∧
      ∀i : Fin (size g),i∈S ↔ e (representative g i)∈W}.ncard=1+size g+secantCount g := by
  have he : {S : Finset (Fin (size g)) | ∃W : Submodule ℂ Mat,Module.finrank ℂ W≤2 ∧
      ∀i : Fin (size g),i∈S ↔ e (representative g i)∈W}=(deletionSets g : Set _) := by
    ext S
    exact (transformed_deletionSets_exact g e S).symm
  rw [he,Set.ncard_coe_finset,deletionSets_card]

end
end Holant.Certificates.PlatonicAtlas
