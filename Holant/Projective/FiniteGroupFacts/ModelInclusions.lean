import Holant.Projective.FiniteGroupFacts.ActualModels
import Mathlib.GroupTheory.IndexNormal

/-! Literal inclusions of the displayed models and their index-two relation. -/
namespace Holant.Projective.FiniteGroupFacts
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Projective.BoundedTorsion
noncomputable section

theorem modelPGL_mono (g h : PlatonicModel)
    (hgh : ∀ U : ComplexMatrix, groupDirection g U → groupDirection h U) :
    modelPGL g ≤ modelPGL h := by
  rintro q ⟨U, hU, rfl⟩
  exact ⟨U, hgh U hU, rfl⟩

theorem tetrahedral_le_octahedral : modelPGL .tetrahedral ≤ modelPGL .octahedral := by
  apply modelPGL_mono
  rintro U ⟨c, hc, V, hV, rfl⟩
  exact ⟨c, hc, V, Or.inl hV, rfl⟩

theorem tetrahedral_le_icosahedral : modelPGL .tetrahedral ≤ modelPGL .icosahedral := by
  apply modelPGL_mono
  rintro U ⟨c, hc, V, hV, rfl⟩
  exact ⟨c, hc, V, Or.inl hV, rfl⟩

theorem tetrahedral_index_in_octahedral :
    ((modelPGL .tetrahedral).subgroupOf (modelPGL .octahedral)).index = 2 := by
  have hc : Nat.card ((modelPGL .tetrahedral).subgroupOf (modelPGL .octahedral)) = 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tetrahedral_le_octahedral).toEquiv]
    exact modelPGL_card _
  have h := Subgroup.index_mul_card ((modelPGL .tetrahedral).subgroupOf (modelPGL .octahedral))
  rw [hc, modelPGL_card] at h
  change _ * 12 = 24 at h
  omega

theorem tetrahedral_normal_in_octahedral :
    ((modelPGL .tetrahedral).subgroupOf (modelPGL .octahedral)).Normal :=
  Subgroup.normal_of_index_eq_two tetrahedral_index_in_octahedral

theorem octahedral_le_normalizer_tetrahedral :
    modelPGL .octahedral ≤ Subgroup.normalizer (modelPGL .tetrahedral : Set (PGL2 ℂ)) := by
  have := tetrahedral_normal_in_octahedral
  exact Subgroup.le_normalizer_of_normal_subgroupOf tetrahedral_le_octahedral

theorem tetrahedral_le_normalizer_icosahedral :
    modelPGL .tetrahedral ≤ Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ)) :=
  tetrahedral_le_icosahedral.trans (modelPGL .icosahedral).le_normalizer

end
end Holant.Projective.FiniteGroupFacts
