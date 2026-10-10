import Holant.Projective.FiniteSubgroupClassification.NormalKlein
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! An elementary recognition theorem for the octahedral group. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
noncomputable section

private theorem order_six_of_commuting_two_three {G : Type*} [Group G]
    (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 3) (hab : Commute a b) :
    orderOf (a * b) = 6 := by
  rw [hab.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ha, hb]; decide), ha, hb]

/-- A normal subgroup of order three in a group of order twenty-four forces
an element of order six. -/
theorem exists_order_six_of_normal_three {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 24) (N : Subgroup G) [N.Normal] (hN : Nat.card N = 3) :
    ∃ g : G, orderOf g = 6 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : IsCyclic N := isCyclic_of_prime_card hN
  let f : G →* MulAut N := MulAut.conjNormal
  have hAut : Nat.card (MulAut N) = 2 := by
    rw [IsCyclic.card_mulAut, hN]
    decide
  have hr := f.range.card_subgroup_dvd_card
  rw [hAut] at hr
  have hk := f.ker.card_mul_index
  rw [Subgroup.index_ker, hG] at hk
  have hkr : 2 ∣ Nat.card f.ker := by
    have hr' : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by
      simpa using (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hr
    rcases hr' with hr' | hr' <;> rw [hr'] at hk <;> omega
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 hkr
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 (by simp [hN])
  have hab : Commute (a : G) (b : G) := by
    have he := congrArg (fun t : MulAut N => (t b : G)) a.property
    change (a : G) * (b : G) * (a : G)⁻¹ = b at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  refine ⟨(a : G) * (b : G), order_six_of_commuting_two_three _ _ ?_ ?_ hab⟩
  · exact (orderOf_injective f.ker.subtype Subtype.coe_injective a).trans ha
  · exact (orderOf_injective N.subtype Subtype.coe_injective b).trans hb

/-- A normal subgroup of order two is central; in an order-twenty-four
group its involution therefore commutes with an element of order three. -/
theorem exists_order_six_of_normal_two {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 24) (N : Subgroup G) [N.Normal] (hN : Nat.card N = 2) :
    ∃ g : G, orderOf g = 6 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : IsCyclic N := isCyclic_of_prime_card hN
  have hAut : Nat.card (MulAut N) = 1 := by
    rw [IsCyclic.card_mulAut, hN]
    decide
  letI : Subsingleton (MulAut N) := (Nat.card_eq_one_iff_unique.mp hAut).1
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 (by simp [hN])
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by simp [hG])
  have hab : Commute (a : G) b := by
    have he := congrArg (fun t : MulAut N => (t a : G))
      (Subsingleton.elim (MulAut.conjNormal b) 1)
    change b * (a : G) * b⁻¹ = a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  refine ⟨(a : G) * b, order_six_of_commuting_two_three _ _ ?_ hb hab⟩
  exact (orderOf_injective N.subtype Subtype.coe_injective a).trans ha

/-- Every Sylow three-subgroup of a group of order twenty-four has order three. -/
theorem sylow_three_card_of_card_twentyfour {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 24) (P : Sylow 3 G) : Nat.card P = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [Sylow.card_eq_multiplicity, hG]
  decide +kernel

/-- Excluding order six rules out the normal Sylow-three possibility. -/
theorem sylow_three_count_of_card_twentyfour {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 24) (h6 : ∀ g : G, orderOf g ≠ 6) :
    Nat.card (Sylow 3 G) = 4 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 G := Classical.choice inferInstance
  have hP := sylow_three_card_of_card_twentyfour hG P
  have hi : P.index = 8 := by
    have h := P.toSubgroup.index_mul_card
    rw [hP, hG] at h
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hle := Nat.le_of_dvd (by decide : 0 < 8) hd
  have hm := card_sylow_modEq_one 3 G
  change Nat.card (Sylow 3 G) % 3 = 1 % 3 at hm
  have hcases : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 ∨
      Nat.card (Sylow 3 G) = 7 := by omega
  rcases hcases with hc | hc | hc
  · letI : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hc).1
    letI : P.Normal := P.normal_of_subsingleton
    obtain ⟨g, hg⟩ := exists_order_six_of_normal_three hG P.toSubgroup hP
    exact False.elim (h6 g hg)
  · exact hc
  · norm_num [hc] at hd

/-- Conjugation on the four Sylow-three subgroups is faithful. -/
theorem sylow_three_action_injective_of_card_twentyfour {G : Type*}
    [Group G] [Finite G] (hG : Nat.card G = 24)
    (h6 : ∀ g : G, orderOf g ≠ 6) :
    Function.Injective (MulAction.toPermHom G (Sylow 3 G)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let f := MulAction.toPermHom G (Sylow 3 G)
  have hcount := sylow_three_count_of_card_twentyfour hG h6
  let P : Sylow 3 G := Classical.choice inferInstance
  have hkn (R : Sylow 3 G) : f.ker ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    have he := congrArg (fun t : Equiv.Perm (Sylow 3 G) => t R) hx
    exact he
  have hnorm : Nat.card (Subgroup.normalizer (P : Set G)) = 6 := by
    have hi := P.card_eq_index_normalizer
    have hc := (Subgroup.normalizer (P : Set G)).index_mul_card
    rw [← hi, hcount, hG] at hc
    omega
  have hkdiv : Nat.card f.ker ∣ 6 := by
    simpa [hnorm] using Subgroup.card_dvd_of_le (hkn P)
  have hknot : ¬3 ∣ Nat.card f.ker := by
    intro hk3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 3 hk3
    have hxG : orderOf (x : G) = 3 :=
      (orderOf_injective f.ker.subtype Subtype.coe_injective x).trans hx
    let Q : Sylow 3 G := Sylow.ofCard (Subgroup.zpowers (x : G)) (by
      rw [Nat.card_zpowers, hxG, hG]
      decide +kernel)
    have hQK : (Q : Subgroup G) ≤ f.ker := by
      change Subgroup.zpowers (x : G) ≤ f.ker
      exact Subgroup.zpowers_le.mpr x.property
    have heq (R : Sylow 3 G) : R = Q := by
      have hQN := hQK.trans (hkn R)
      have hQR : (Q : Subgroup G) ≤ R := by
        have h := Q.isPGroup'.inf_normalizer_sylow R
        rw [inf_eq_left.mpr hQN] at h
        exact inf_eq_left.mp h.symm
      exact Sylow.ext (Q.is_maximal' R.isPGroup' hQR)
    have : Subsingleton (Sylow 3 G) := ⟨fun R S => (heq R).trans (heq S).symm⟩
    have hone : Nat.card (Sylow 3 G) = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨this, inferInstance⟩
    omega
  have hkcases : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 := by
    have hkpos : 0 < Nat.card f.ker := Nat.card_pos
    have hkle := Nat.le_of_dvd (by decide : 0 < 6) hkdiv
    interval_cases h : Nat.card f.ker <;> norm_num [h] at *
  have hkone : Nat.card f.ker = 1 := by
    rcases hkcases with h | h
    · exact h
    · obtain ⟨g, hg⟩ := exists_order_six_of_normal_two hG f.ker h
      exact False.elim (h6 g hg)
  exact f.ker_eq_bot_iff.mp (f.ker.eq_bot_of_card_eq hkone)

/-- A group of order twenty-four without an element of order six is `S4`.
The proof uses its actual conjugation action on its Sylow-three subgroups. -/
theorem nonempty_mulEquiv_S4_of_card_twentyfour {G : Type*} [Group G]
    (hG : Nat.card G = 24) (h6 : ∀ g : G, orderOf g ≠ 6) :
    Nonempty (G ≃* S4) := by
  letI : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have hc := sylow_three_count_of_card_twentyfour hG h6
  let e : Sylow 3 G ≃ Fin 4 :=
    (Nat.equivFinOfCardPos (by omega)).trans (finCongr hc)
  let f : G →* S4 := e.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom G (Sylow 3 G))
  have hf : Function.Injective f := e.permCongrHom.injective.comp
    (sylow_three_action_injective_of_card_twentyfour hG h6)
  have hS4 : Nat.card S4 = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num [Nat.factorial]
  exact ⟨MulEquiv.ofBijective f (hf.bijective_of_nat_card_le (by omega))⟩

/-- Pulling back the usual Klein four in `S4` gives an actual normal
Klein four in the ambient scalar quotient. -/
theorem exists_normal_klein_of_mulEquiv_S4
    (H : Subgroup (PGL2 ℂ)) (e : H ≃* S4) :
    ∃ K : Subgroup (PGL2 ℂ), K ≤ H ∧ IsKleinFour K ∧ (K.subgroupOf H).Normal := by
  letI : IsKleinFour s4KleinFour := s4_kleinFour_isKleinFour
  letI : s4KleinFour.Normal := s4_kleinFour_normal
  let S : Subgroup H := s4KleinFour.map e.symm.toMonoidHom
  letI : IsKleinFour S := kleinFour_of_mulEquiv
    (Subgroup.equivMapOfInjective s4KleinFour e.symm.toMonoidHom e.symm.injective).symm
  letI : S.Normal := Subgroup.Normal.map inferInstance _ e.symm.surjective
  let K : Subgroup (PGL2 ℂ) := S.map H.subtype
  have hKH : K ≤ H := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hKS : K.subgroupOf H = S :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective S
  refine ⟨K, hKH, ?_, ?_⟩
  · exact kleinFour_of_mulEquiv
      (Subgroup.equivMapOfInjective S H.subtype H.subtype_injective).symm
  · rw [hKS]
    infer_instance

/-- The octahedral conjugacy conclusion follows from the group order and
the exclusion of elements of order six. -/
theorem card_twentyfour_no_order_six_conjugacy
    (H : Subgroup (PGL2 ℂ)) (hH : Nat.card H = 24)
    (h6 : ∀ g : H, orderOf g ≠ 6) :
    ∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom = modelPGL .octahedral := by
  obtain ⟨e⟩ := nonempty_mulEquiv_S4_of_card_twentyfour hH h6
  obtain ⟨K, hKH, hK, hnormal⟩ := exists_normal_klein_of_mulEquiv_S4 H e
  letI : IsKleinFour K := hK
  letI : (K.subgroupOf H).Normal := hnormal
  exact normal_klein_card_twentyfour_conjugacy H K hKH hH

end
end Holant.Projective.FiniteSubgroupClassification
