import Holant.Projective.FiniteSubgroupClassification.KleinConjugacy

/-! Actual tetrahedral and octahedral conjugacy from a normal projective Klein
four subgroup. The normal Klein four is an explicit hypothesis here; deriving
it for arbitrary finite subgroups is part of the remaining classification. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

theorem card_conjugate_subgroup (H : Subgroup (PGL2 ℂ)) (g : PGL2 ℂ) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  (Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv).symm

/-- A projective group with a normal Klein four is conjugate into the actual
octahedral matrix model. -/
theorem normal_klein_conjugate_le_octahedral
    (H K : Subgroup (PGL2 ℂ)) (hKH : K ≤ H)
    [IsKleinFour K] [(K.subgroupOf H).Normal] :
    ∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom ≤ modelPGL .octahedral := by
  obtain ⟨g, hg⟩ := kleinFour_conjugacy K
  refine ⟨g, ?_⟩
  rw [← pauli_normalizer, ← hg]
  exact (Subgroup.map_mono (Subgroup.le_normalizer_of_normal_subgroupOf hKH)).trans
    (Subgroup.le_normalizer_map (MulAut.conj g).toMonoidHom)

/-- The actual tetrahedral model is the unique index-two subgroup of the
actual octahedral model. -/
theorem octahedral_unique_index_two (S : Subgroup (modelPGL .octahedral))
    (hS : S.index = 2) : S = (modelPGL .tetrahedral).subgroupOf (modelPGL .octahedral) := by
  let T := (modelPGL .tetrahedral).subgroupOf (modelPGL .octahedral)
  have hs : (S.map octahedral_iso_S4.toMonoidHom).index = 2 := by
    exact (S.index_map_equiv octahedral_iso_S4).trans hS
  have ht : (T.map octahedral_iso_S4.toMonoidHom).index = 2 := by
    exact (T.index_map_equiv octahedral_iso_S4).trans tetrahedral_index_in_octahedral
  have he : S.map octahedral_iso_S4.toMonoidHom = T.map octahedral_iso_S4.toMonoidHom :=
    (s4_unique_index_two _ hs).trans (s4_unique_index_two _ ht).symm
  exact Subgroup.map_injective octahedral_iso_S4.injective he

/-- A subgroup of the octahedral model with twelve elements is the displayed
tetrahedral model itself. -/
theorem subgroup_octahedral_card_twelve
    (H : Subgroup (PGL2 ℂ)) (hHO : H ≤ modelPGL .octahedral) (hcard : Nat.card H = 12) :
    H = modelPGL .tetrahedral := by
  let S := H.subgroupOf (modelPGL .octahedral)
  have hS : Nat.card S = 12 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHO).toEquiv).trans hcard
  have hi : S.index = 2 := by
    have he := S.index_mul_card
    rw [hS, modelPGL_card] at he
    change S.index * 12 = 24 at he
    omega
  have he := congrArg (fun T : Subgroup (modelPGL .octahedral) =>
      T.map (modelPGL .octahedral).subtype) (octahedral_unique_index_two S hi)
  simpa only [S, Subgroup.map_subgroupOf_eq_of_le hHO,
    Subgroup.map_subgroupOf_eq_of_le tetrahedral_le_octahedral] using he

/-- Normal Klein four plus order twelve gives genuine tetrahedral conjugacy. -/
theorem normal_klein_card_twelve_conjugacy
    (H K : Subgroup (PGL2 ℂ)) (hKH : K ≤ H)
    [IsKleinFour K] [(K.subgroupOf H).Normal] (hcard : Nat.card H = 12) :
    ∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom = modelPGL .tetrahedral := by
  obtain ⟨g, hg⟩ := normal_klein_conjugate_le_octahedral H K hKH
  exact ⟨g, subgroup_octahedral_card_twelve _ hg
    ((card_conjugate_subgroup H g).trans hcard)⟩

/-- Normal Klein four plus order twenty-four gives genuine octahedral conjugacy. -/
theorem normal_klein_card_twentyfour_conjugacy
    (H K : Subgroup (PGL2 ℂ)) (hKH : K ≤ H)
    [IsKleinFour K] [(K.subgroupOf H).Normal] (hcard : Nat.card H = 24) :
    ∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom = modelPGL .octahedral := by
  obtain ⟨g, hg⟩ := normal_klein_conjugate_le_octahedral H K hKH
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [card_conjugate_subgroup, hcard, modelPGL_card]
  rfl

end
end Holant.Projective.FiniteSubgroupClassification
