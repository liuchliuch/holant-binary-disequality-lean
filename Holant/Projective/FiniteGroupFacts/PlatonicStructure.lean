import Holant.Projective.FiniteGroupFacts.PlatonicOrders
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-! Structural assertions about the genuine permutation groups in source
Lemma 2.2(iii–v). The Klein four subgroup is identified by actual involutions. -/
namespace Holant.Projective.FiniteGroupFacts
open Equiv Equiv.Perm Subgroup

/-- An involution has exact order two; the identity is excluded. -/
def Involution {G : Type*} [Group G] (g : G) : Prop := g * g = 1 ∧ g ≠ 1
instance {G : Type*} [Group G] [DecidableEq G] (g : G) : Decidable (Involution g) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem involution_iff_orderOf {G : Type*} [Group G] (g : G) :
    Involution g ↔ orderOf g = 2 := by
  simpa only [Involution, pow_two] using (orderOf_eq_prime_iff (x := g) (p := 2)).symm

/-- Exactly two disjoint cycles, both of length two. -/
def DoubleTransposition {n : ℕ} (g : Equiv.Perm (Fin n)) : Prop := g.cycleType = {2, 2}
instance {n : ℕ} (g : Equiv.Perm (Fin n)) : Decidable (DoubleTransposition g) :=
  inferInstanceAs (Decidable (g.cycleType = {2, 2}))

/-- A single cycle of length two. -/
def Transposition {n : ℕ} (g : Equiv.Perm (Fin n)) : Prop := g.cycleType = {2}
instance {n : ℕ} (g : Equiv.Perm (Fin n)) : Decidable (Transposition g) :=
  inferInstanceAs (Decidable (g.cycleType = {2}))

theorem transposition_iff_isSwap {n : ℕ} (g : Equiv.Perm (Fin n)) :
    Transposition g ↔ g.IsSwap := isSwap_iff_cycleType.symm

private theorem even_involution_cycleType {n : ℕ} (hn : n ≤ 5)
    (g : alternatingGroup (Fin n)) (hg : Involution g) :
    (g : Equiv.Perm (Fin n)).cycleType = {2, 2} := by
  have ho : orderOf (g : Equiv.Perm (Fin n)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact (involution_iff_orderOf g).mp hg
  obtain ⟨k, hk⟩ := cycleType_prime_order (show (orderOf (g : Equiv.Perm (Fin n))).Prime by
    rw [ho]; exact Nat.prime_two)
  rw [ho] at hk
  have hs := (g : Equiv.Perm (Fin n)).sum_cycleType_le
  rw [hk, Multiset.sum_replicate] at hs
  simp only [smul_eq_mul, Fintype.card_fin] at hs
  have hk1 : k ≤ 1 := by omega
  have hsign := g.property
  rw [mem_alternatingGroup, sign_of_cycleType, hk] at hsign
  interval_cases k
  · exact False.elim ((by decide : (-1 : ℤˣ) ^ 3 ≠ 1) hsign)
  · simpa using hk

theorem a4_involution_double_transposition (g : A4) :
    Involution g ↔ DoubleTransposition g.val := by
  constructor
  · exact even_involution_cycleType (by omega) g
  · intro h
    rw [involution_iff_orderOf, ← Subgroup.orderOf_coe, ← lcm_cycleType]
    simp [DoubleTransposition] at h
    rw [h]
    norm_num [Nat.factorial]

theorem a5_involution_double_transposition (g : A5) :
    Involution g ↔ DoubleTransposition g.val := by
  constructor
  · exact even_involution_cycleType (by omega) g
  · intro h
    rw [involution_iff_orderOf, ← Subgroup.orderOf_coe, ← lcm_cycleType]
    change g.val.cycleType = {2, 2} at h
    rw [h]
    norm_num [Nat.factorial]

theorem s4_involution_types (g : S4) :
    Involution g ↔ Transposition g ∨ DoubleTransposition g := by
  constructor
  · intro hg
    have ho := (involution_iff_orderOf g).mp hg
    obtain ⟨k, hk⟩ := cycleType_prime_order (show (orderOf g).Prime by
      rw [ho]; exact Nat.prime_two)
    rw [ho] at hk
    have hs := g.sum_cycleType_le
    rw [hk, Multiset.sum_replicate] at hs
    simp only [smul_eq_mul, Fintype.card_fin] at hs
    have hk1 : k ≤ 1 := by omega
    interval_cases k
    · exact Or.inl (by simpa [Transposition] using hk)
    · exact Or.inr (by simpa [DoubleTransposition] using hk)
  · rintro (h | h) <;> rw [involution_iff_orderOf, ← lcm_cycleType]
    · change g.cycleType = {2} at h
      rw [h]; norm_num
    · change g.cycleType = {2, 2} at h
      rw [h]; norm_num

theorem s4_transposition_count :
    ((Finset.univ : Finset S4).filter Transposition).card = 6 := by
  change ((Finset.univ : Finset S4).filter fun g => g.cycleType = {2}).card = 6
  rw [Equiv.Perm.card_of_cycleType]
  norm_num [Nat.factorial]

theorem s4_double_transposition_count :
    ((Finset.univ : Finset S4).filter DoubleTransposition).card = 3 := by
  change ((Finset.univ : Finset S4).filter fun g => g.cycleType = {2, 2}).card = 3
  rw [Equiv.Perm.card_of_cycleType]
  norm_num [Nat.factorial]

theorem s4_unique_index_two (H : Subgroup S4) (hH : H.index = 2) :
    H = alternatingGroup (Fin 4) := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hH

theorem s4_alternating_index_two : (alternatingGroup (Fin 4)).index = 2 :=
  alternatingGroup.index_eq_two

theorem a5_simple : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)

theorem a5_no_index_two (H : Subgroup A5) : H.index ≠ 2 := by
  intro h
  have : IsSimpleGroup A5 := a5_simple
  rcases (Subgroup.normal_of_index_eq_two h).eq_bot_or_eq_top with rfl | rfl
  · have hc : Nat.card A5 = 60 := by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
    rw [Subgroup.index_bot, hc] at h
    omega
  · simp at h

abbrev a4KleinFour : Subgroup A4 := alternatingGroup.kleinFour (Fin 4)

theorem a4_kleinFour_normal : a4KleinFour.Normal :=
  alternatingGroup.normal_kleinFour (by simp)

theorem a4_kleinFour_isKleinFour : IsKleinFour a4KleinFour :=
  alternatingGroup.kleinFour_isKleinFour (by simp)


set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem a4_mem_kleinFour (g : A4) : g ∈ a4KleinFour ↔ g = 1 ∨ Involution g := by
  change g ∈ (a4KleinFour : Set A4) ↔ _
  rw [alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)]
  simpa [DoubleTransposition] using (or_congr Iff.rfl (a4_involution_double_transposition g).symm)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem a4_involution_centralizer (g : A4) (hg : Involution g) :
    Subgroup.centralizer {g} = a4KleinFour := by
  have hc : ∀ g h : A4, Involution g → (g * h = h * g ↔ h = 1 ∨ Involution h) := by
    decide +kernel
  ext h
  rw [Subgroup.mem_centralizer_singleton_iff, a4_mem_kleinFour]
  exact (eq_comm.trans (hc g h hg))

theorem a4_unique_kleinFour (H : Subgroup A4) [IsKleinFour H] : H = a4KleinFour := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro g hg
    rw [a4_mem_kleinFour]
    by_cases h : g = 1
    · exact Or.inl h
    · refine Or.inr ⟨?_, h⟩
      exact congrArg Subtype.val (IsKleinFour.mul_self (⟨g, hg⟩ : H))
  · rw [alternatingGroup.kleinFour_card_of_card_eq_four (by simp),
      IsKleinFour.card_four (G := H)]

/-- Cardinality of the actual centralizer, expressed by a finite membership test. -/
theorem centralizer_card_eq {G : Type*} [Group G] [Fintype G] [DecidableEq G] (g : G) :
    Nat.card (Subgroup.centralizer {g}) =
      ((Finset.univ : Finset G).filter fun h => g * h = h * g).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext h
  simp [Subgroup.mem_centralizer_singleton_iff, eq_comm]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s4_transposition_centralizer_card (g : S4) (hg : Transposition g) :
    Nat.card (Subgroup.centralizer {g}) = 4 := by
  rw [Equiv.Perm.nat_card_centralizer]
  change g.cycleType = {2} at hg
  rw [hg]
  norm_num [Nat.factorial]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s4_double_transposition_centralizer_card (g : S4) (hg : DoubleTransposition g) :
    Nat.card (Subgroup.centralizer {g}) = 8 := by
  rw [Equiv.Perm.nat_card_centralizer]
  change g.cycleType = {2, 2} at hg
  rw [hg]
  norm_num [Nat.factorial]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem a5_involution_centralizer_card (g : A5) (hg : Involution g) :
    Nat.card (Subgroup.centralizer {g}) = 4 := by
  rw [centralizer_card_eq]
  have h : ∀ g : A5, Involution g →
      ((Finset.univ : Finset A5).filter fun h => g * h = h * g).card = 4 := by decide +kernel
  exact h g hg

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem a5_involution_centralizer_square (g : A5) (hg : Involution g)
    (h : Subgroup.centralizer {g}) : h ^ 2 = 1 := by
  have hs : ∀ g h : A5, Involution g → g * h = h * g → h * h = 1 := by decide +kernel
  apply Subtype.ext
  exact hs g h hg ((Subgroup.mem_centralizer_singleton_iff).mp h.property).symm

theorem a5_involution_centralizer_kleinFour (g : A5) (hg : Involution g) :
    IsKleinFour (Subgroup.centralizer {g}) where
  card_four := a5_involution_centralizer_card g hg
  exponent_two := by
    have hd : Monoid.exponent (Subgroup.centralizer {g}) ∣ 2 := by
      rw [Monoid.exponent_dvd]
      intro h
      exact orderOf_dvd_of_pow_eq_one (a5_involution_centralizer_square g hg h)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · have he := Monoid.exp_eq_one_iff.mp h
      have hc : Nat.card (Subgroup.centralizer {g}) ≤ 1 :=
        (@Finite.card_le_one_iff_subsingleton (Subgroup.centralizer {g}) _).mpr he
      rw [a5_involution_centralizer_card g hg] at hc
      omega
    · exact h


set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem a4_no_index_two (H : Subgroup A4) : H.index ≠ 2 := by
  intro hi
  have h3 : ∀ g : A4, g ^ 3 = 1 → g ∈ H := by
    intro g hg
    have h2 := H.mul_self_mem_of_index_two hi g
    apply (H.mul_mem_cancel_left h2).mp
    have he : (g * g) * g = 1 := by simpa [pow_succ, pow_two] using hg
    rw [he]
    exact H.one_mem
  have hex : ∀ g : A4, ∃ a b : A4, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ g = a * b := by
    decide +kernel
  have ht : H = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨a, b, ha, hb, rfl⟩ := hex g
    exact H.mul_mem (h3 a ha) (h3 b hb)
  simp [ht] at hi


/-- A concrete member of the single A₅ involution class. -/
def a5BaseInvolution : A5 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by change Equiv.Perm.sign _ = 1; decide +kernel⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem a5_involution_conjugate_base (g : A5) (hg : Involution g) :
    IsConj a5BaseInvolution g := by
  rw [isConj_iff]
  have h : ∀ g : A5, Involution g →
      ∃ c : A5, c * a5BaseInvolution * c⁻¹ = g := by decide +kernel
  exact h g hg

theorem a5_involutions_one_class (g h : A5) (hg : Involution g) (hh : Involution h) :
    IsConj g h := (a5_involution_conjugate_base g hg).symm.trans
      (a5_involution_conjugate_base h hh)

/-- The actual Klein four subgroup of S₄, embedded from A₄. -/
def s4KleinFour : Subgroup S4 := a4KleinFour.map (alternatingGroup (Fin 4)).subtype

theorem s4_mem_kleinFour (g : S4) : g ∈ s4KleinFour ↔ g = 1 ∨ DoubleTransposition g := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases (a4_mem_kleinFour a).mp ha with rfl | ha
    · exact Or.inl rfl
    · exact Or.inr ((a4_involution_double_transposition a).mp ha)
  · rintro (rfl | hg)
    · exact s4KleinFour.one_mem
    · have hga : g ∈ alternatingGroup (Fin 4) :=
        Equiv.Perm.cycleType_eq_two_two_subset_alternatingGroup hg
      refine ⟨⟨g, hga⟩, ?_, rfl⟩
      exact (a4_mem_kleinFour _).mpr (Or.inr ((a4_involution_double_transposition _).mpr hg))

theorem s4_kleinFour_normal : s4KleinFour.Normal where
  conj_mem := by
    intro g hg c
    rw [s4_mem_kleinFour] at hg ⊢
    rcases hg with rfl | hg
    · exact Or.inl (by simp)
    · exact Or.inr (by simpa [DoubleTransposition, cycleType_conj] using hg)

noncomputable def a4KleinFourIsoS4KleinFour : a4KleinFour ≃* s4KleinFour :=
  Subgroup.equivMapOfInjective a4KleinFour (alternatingGroup (Fin 4)).subtype Subtype.val_injective

theorem s4_kleinFour_card : Nat.card s4KleinFour = 4 := by
  rw [← Nat.card_congr a4KleinFourIsoS4KleinFour.toEquiv]
  exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)


theorem s4_kleinFour_isKleinFour : IsKleinFour s4KleinFour where
  card_four := s4_kleinFour_card
  exponent_two := by
    rw [← Monoid.exponent_eq_of_mulEquiv a4KleinFourIsoS4KleinFour]
    exact alternatingGroup.exponent_kleinFour_of_card_eq_four (by simp)

theorem s4_unique_normal_kleinFour (H : Subgroup S4) [H.Normal] [IsKleinFour H] :
    H = s4KleinFour := by
  have hno : ∀ g ∈ H, ¬g.IsSwap := by
    intro g hg hswap
    have ht : H = ⊤ := by
      rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
      intro h hh
      have hc : IsConj g h := isConj_iff_cycleType_eq.mpr
        ((isSwap_iff_cycleType.mp hswap).trans (isSwap_iff_cycleType.mp hh).symm)
      obtain ⟨c, rfl⟩ := isConj_iff.mp hc
      exact (inferInstance : H.Normal).conj_mem g hg c
    have hc := IsKleinFour.card_four (G := H)
    rw [ht, Subgroup.card_top, Nat.card_perm, Nat.card_fin] at hc
    norm_num [Nat.factorial] at hc
  apply Subgroup.eq_of_le_of_card_ge
  · intro g hg
    rw [s4_mem_kleinFour]
    by_cases h : g = 1
    · exact Or.inl h
    have hi : Involution g := ⟨congrArg Subtype.val (IsKleinFour.mul_self (⟨g, hg⟩ : H)), h⟩
    rcases (s4_involution_types g).mp hi with hs | hd
    · exact False.elim (hno g hg ((transposition_iff_isSwap g).mp hs))
    · exact Or.inr hd
  · rw [s4_kleinFour_card, IsKleinFour.card_four (G := H)]

theorem s4_double_transposition_iff (g : S4) :
    DoubleTransposition g ↔ Involution g ∧ Equiv.Perm.sign g = 1 := by
  constructor
  · intro hg
    have ha : g ∈ alternatingGroup (Fin 4) :=
      cycleType_eq_two_two_subset_alternatingGroup hg
    have hi := (a4_involution_double_transposition ⟨g, ha⟩).mpr hg
    exact ⟨⟨congrArg Subtype.val hi.1, fun h => hi.2 (Subtype.ext h)⟩, ha⟩
  · rintro ⟨hg, ha⟩
    exact (a4_involution_double_transposition ⟨g, ha⟩).mp
      ⟨Subtype.ext hg.1, fun h => hg.2 (congrArg Subtype.val h)⟩

end Holant.Projective.FiniteGroupFacts
