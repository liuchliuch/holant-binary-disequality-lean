import Holant.Proofs.FiniteGroups.ModelRigidity


namespace Holant.LocalDrafts.FinitePGL2

open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteSubgroupClassification
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit

noncomputable section

/-- The dihedral parameter is the rotation order: its group order is `2*m`. -/
inductive ModelType where
  | cyclic (m : ℕ)
  | dihedral (m : ℕ)
  | platonic (p : PlatonicModel)
  deriving DecidableEq

/-- Literal ambient conjugacy, including the source's parameter restrictions. -/
def HasModel (H : Subgroup (PGL2 ℂ)) : ModelType → Prop
  | .cyclic m => 0 < m ∧ ∃ ω : ℂˣ, IsPrimitiveRoot ω m ∧
      ConjugateTo H (cyclicModel ω)
  | .dihedral m => 2 ≤ m ∧ ∃ ω : ℂˣ, IsPrimitiveRoot ω m ∧
      ConjugateTo H (dihedralModel ω)
  | .platonic p => ConjugateTo H (modelPGL p)

theorem exists_model (H : Subgroup (PGL2 ℂ)) [Finite H] :
    ∃ t : ModelType, HasModel H t := by
  rcases finite_subgroup_classification H with h | h
  · rcases h with ⟨g, ω, m, hm, hω, he⟩ | ⟨g, ω, m, hm, hω, he⟩ | h | h
    · exact ⟨.cyclic m, hm, ω, hω, g, he⟩
    · exact ⟨.dihedral m, hm, ω, hω, g, he⟩
    · exact ⟨.platonic .tetrahedral, h⟩
    · exact ⟨.platonic .octahedral, h⟩
  · exact ⟨.platonic .icosahedral, h⟩

/-- Compare two actual targets of conjugacy from the same subgroup. -/
theorem targets_nonempty_mulEquiv {G : Type*} [Group G] {H K L : Subgroup G}
    (hK : ConjugateTo H K) (hL : ConjugateTo H L) : Nonempty (K ≃* L) := by
  obtain ⟨eK⟩ := hK.nonempty_mulEquiv
  obtain ⟨eL⟩ := hL.nonempty_mulEquiv
  exact ⟨eK.symm.trans eL⟩

/-- Pairwise disjointness of all five families, with uniqueness of the integer
parameter.  Finiteness of H is unnecessary once the two actual models exist. -/
theorem model_type_unique {H : Subgroup (PGL2 ℂ)} {s t : ModelType}
    (hs : HasModel H s) (ht : HasModel H t) : s = t := by
  cases s with
  | cyclic m =>
      obtain ⟨_, ω, hω, hHω⟩ := hs
      cases t with
      | cyclic n =>
          obtain ⟨_, ν, hν, hHν⟩ := ht
          have hc := hHω.card_eq.symm.trans hHν.card_eq
          rw [cyclicModel_card, cyclicModel_card, ← hω.eq_orderOf, ← hν.eq_orderOf] at hc
          exact congrArg ModelType.cyclic hc
      | dihedral n =>
          obtain ⟨hn, ν, hν, hHν⟩ := ht
          exact (cyclicModel_not_mulEquiv_dihedral ω hn hν
            (targets_nonempty_mulEquiv hHω hHν)).elim
      | platonic p =>
          exact (cyclicModel_not_mulEquiv_platonic ω p
            (targets_nonempty_mulEquiv hHω ht)).elim
  | dihedral m =>
      obtain ⟨hm, ω, hω, hHω⟩ := hs
      cases t with
      | cyclic n =>
          obtain ⟨_, ν, hν, hHν⟩ := ht
          exact (cyclicModel_not_mulEquiv_dihedral ν hm hω
            (targets_nonempty_mulEquiv hHν hHω)).elim
      | dihedral n =>
          obtain ⟨_, ν, hν, hHν⟩ := ht
          have hc := hHω.card_eq.symm.trans hHν.card_eq
          rw [dihedralModel_card hω, dihedralModel_card hν] at hc
          exact congrArg ModelType.dihedral (by omega : m = n)
      | platonic p =>
          exact (dihedralModel_not_mulEquiv_platonic hω p
            (targets_nonempty_mulEquiv hHω ht)).elim
  | platonic p =>
      cases t with
      | cyclic n =>
          obtain ⟨_, ν, hν, hHν⟩ := ht
          exact (cyclicModel_not_mulEquiv_platonic ν p
            (targets_nonempty_mulEquiv hHν hs)).elim
      | dihedral n =>
          obtain ⟨_, ν, hν, hHν⟩ := ht
          exact (dihedralModel_not_mulEquiv_platonic hν p
            (targets_nonempty_mulEquiv hHν hs)).elim
      | platonic q =>
          exact congrArg ModelType.platonic
            (platonic_eq_of_card_eq (hs.card_eq.symm.trans ht.card_eq))

/-- Proposed source-level classification interface: exactly one of C_m
(m ≥ 1), D_{2m} (m ≥ 2), T, O, I, with actual ambient conjugacy.
The conclusion is a structural classification of the stated group actions. -/
theorem finite_subgroup_exists_unique_model (H : Subgroup (PGL2 ℂ)) [Finite H] :
    ∃! t : ModelType, HasModel H t := by
  obtain ⟨t, ht⟩ := exists_model H
  exact ⟨t, ht, fun s hs => model_type_unique hs ht⟩

end
end Holant.LocalDrafts.FinitePGL2
