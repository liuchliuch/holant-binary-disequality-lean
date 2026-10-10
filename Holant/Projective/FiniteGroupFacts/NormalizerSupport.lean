import Holant.Projective.FiniteGroupFacts.Conjugacy

/-! General group-theoretic support for the concrete normalizer calculation.
These lemmas do not assume a finite-projective-group classification. -/
namespace Holant.Projective.FiniteGroupFacts
open Subgroup

variable {G H : Type*} [Group G] [Group H]

theorem kleinFour_of_mulEquiv (e : G ≃* H) [IsKleinFour H] : IsKleinFour G where
  card_four := (Nat.card_congr e.toEquiv).trans IsKleinFour.card_four
  exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two

theorem s4_kleinFour_characteristic : s4KleinFour.Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro e
  have : s4KleinFour.Normal := s4_kleinFour_normal
  have : IsKleinFour s4KleinFour := s4_kleinFour_isKleinFour
  have : (s4KleinFour.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ e.surjective
  have : IsKleinFour (s4KleinFour.map e.toMonoidHom) :=
    kleinFour_of_mulEquiv (Subgroup.equivMapOfInjective s4KleinFour e.toMonoidHom e.injective).symm
  exact s4_unique_normal_kleinFour _

theorem characteristic_comap_equiv (e : G ≃* H) (K : Subgroup H) [K.Characteristic] :
    (K.comap e.toMonoidHom).Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro φ x hx
  have h := Subgroup.characteristic_iff_le_comap.mp (inferInstance : K.Characteristic)
    ((e.symm.trans φ).trans e) hx
  simpa using h

theorem normalizer_le_of_characteristic (K L : Subgroup G) (hKL : K ≤ L)
    [(K.subgroupOf L).Characteristic] : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro n hn k hk
  let φ := L.normalizerMonoidHom ⟨n, hn⟩
  have h := Subgroup.characteristic_iff_le_comap.mp
    (inferInstance : (K.subgroupOf L).Characteristic) φ
    (show (⟨k, hKL hk⟩ : L) ∈ K.subgroupOf L from hk)
  exact h

/-- If two elements induce the same conjugation on generators, their quotient
lies in the centralizer of the generated subgroup. -/
theorem inv_mul_mem_centralizer_of_same_conjugation (x z a b : G)
    (hx : a * x * a⁻¹ = b * x * b⁻¹) (hz : a * z * a⁻¹ = b * z * b⁻¹) :
    a⁻¹ * b ∈ Subgroup.centralizer (Subgroup.closure ({x, z} : Set G)) := by
  rw [Subgroup.centralizer_closure]
  intro t ht
  have h (t : G) (ht : a * t * a⁻¹ = b * t * b⁻¹) :
      t * (a⁻¹ * b) = (a⁻¹ * b) * t := by
    have he := congrArg (fun q : G => a⁻¹ * q * b) ht
    simpa [mul_assoc] using he
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl
  · exact h _ hx
  · exact h _ hz

/-- A concrete subgroup that realizes every ordered generator image accounts
for the full normalizer of a self-centralizing generated subgroup. -/
theorem normalizer_eq_of_generator_action (x z : G) (L : Subgroup G)
    (hVL : Subgroup.closure ({x, z} : Set G) ≤ L)
    (hself : Subgroup.centralizer (Subgroup.closure ({x, z} : Set G)) =
      Subgroup.closure ({x, z} : Set G))
    (hLN : L ≤ Subgroup.normalizer (Subgroup.closure ({x, z} : Set G)))
    (haction : ∀ n ∈ Subgroup.normalizer (Subgroup.closure ({x, z} : Set G)),
      ∃ a ∈ L, a * x * a⁻¹ = n * x * n⁻¹ ∧ a * z * a⁻¹ = n * z * n⁻¹) :
    Subgroup.normalizer (Subgroup.closure ({x, z} : Set G)) = L := by
  apply le_antisymm _ hLN
  intro n hn
  obtain ⟨a, ha, hx, hz⟩ := haction n hn
  have hc := inv_mul_mem_centralizer_of_same_conjugation x z a n hx hz
  rw [hself] at hc
  have hm := L.mul_mem ha (hVL hc)
  simpa using hm

end Holant.Projective.FiniteGroupFacts
