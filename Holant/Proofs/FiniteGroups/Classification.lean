import Holant.Projective.FiniteSubgroupClassification.Reduction
import Holant.Projective.FiniteSubgroupClassification.IcosahedralStructure
import Holant.Projective.FiniteSubgroupClassification.TriangleGenerators
import Holant.Projective.FiniteSubgroupClassification.TriangleTargets
import Holant.Projective.FiniteGroupFacts.PauliModels


namespace Holant.LocalDrafts.FinitePGL2

open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Projective.FiniteSubgroupClassification
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Ambient conjugacy of actual subgroups; this does not assert a classification. -/
def ConjugateTo {G : Type*} [Group G] (H K : Subgroup G) : Prop :=
  ∃ g : G, H.map (MulAut.conj g).toMonoidHom = K

/-- A specified ambient conjugacy gives the underlying group isomorphism. -/
def conjugacyEquiv {G : Type*} [Group G] (H K : Subgroup G) (g : G)
    (hg : H.map (MulAut.conj g).toMonoidHom = K) : H ≃* K :=
  (H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr hg)

theorem ConjugateTo.nonempty_mulEquiv {G : Type*} [Group G] {H K : Subgroup G}
    (h : ConjugateTo H K) : Nonempty (H ≃* K) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨conjugacyEquiv H K g hg⟩

theorem ConjugateTo.card_eq {G : Type*} [Group G] {H K : Subgroup G}
    (h : ConjugateTo H K) : Nat.card H = Nat.card K := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  exact Nat.card_congr e.toEquiv

/-- Closure of the actual two generators supplies inclusion after conjugation;
the independently established order sixty upgrades inclusion to equality. -/
theorem triangle_generated_card_sixty_conjugacy (H : Subgroup (PGL2 ℂ))
    (hcard : Nat.card H = 60) (a b : PGL2 ℂ)
    (ha : orderOf a = 2) (hb : orderOf b = 3) (hab : orderOf (a * b) = 5)
    (hgen : Subgroup.closure ({a, b} : Set (PGL2 ℂ)) = H) :
    ConjugateTo H (modelPGL .icosahedral) := by
  obtain ⟨g, hga, hgb⟩ := triangle_pair_conjugate_into_icosahedral ha hb hab
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ modelPGL .icosahedral := by
    rw [← hgen, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    intro q hq
    rcases (show q = (MulAut.conj g) a ∨ q = (MulAut.conj g) b by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      exact hq) with rfl | rfl
    · change g * a * g⁻¹ ∈ modelPGL .icosahedral
      rw [hga]
      exact pauli_le_model .icosahedral zClass_mem_pauli
    · exact hgb
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard,
    modelPGL_card]
  norm_num [size]

/-- No conjugacy hypothesis is needed to upgrade an abstract A5 identification. -/
theorem a5_subgroup_conjugacy (H : Subgroup (PGL2 ℂ)) (e : H ≃* A5) :
    ConjugateTo H (modelPGL .icosahedral) := by
  have hc : Nat.card H = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨a, b, _, _, ha, hb, hab, hgen⟩ := exists_projective_triangle_generators H e
  exact triangle_generated_card_sixty_conjugacy H hc a b ha hb hab hgen

/-- The remaining geometric branch of the existing reduction is conjugate to
the actual golden-ratio model, not merely abstractly isomorphic to A5. -/
theorem exceptional_235_conjugacy (H : Subgroup (PGL2 ℂ))
    (hcard : Nat.card H = 60) (e : Fin 3 ≃ ExceptionalOrbits H)
    (h0 : stabilizerOrder H (e 0) = 2)
    (h1 : stabilizerOrder H (e 1) = 3)
    (h2 : stabilizerOrder H (e 2) = 5) :
    ConjugateTo H (modelPGL .icosahedral) := by
  obtain ⟨f⟩ := exceptional_235_nonempty_mulEquiv_A5 H hcard e h0 h1 h2
  exact a5_subgroup_conjugacy H f

/-- Existence half of Proposition 2.1, from finiteness alone. -/
theorem finite_subgroup_classification (H : Subgroup (PGL2 ℂ)) [Finite H] :
    ClassifiedWithoutIcosahedral H ∨ ConjugateTo H (modelPGL .icosahedral) := by
  rcases finite_subgroup_reduction H with h | ⟨hc, e, h0, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (exceptional_235_conjugacy H hc e h0 h1 h2)

end
end Holant.LocalDrafts.FinitePGL2
