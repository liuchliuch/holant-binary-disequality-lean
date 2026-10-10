import Holant.Proofs.FiniteGroups.Classification


namespace Holant.LocalDrafts.FinitePGL2

open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Projective.FiniteSubgroupClassification
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit

noncomputable section

/-- Changing the primitive root does not even change the standard subgroup. -/
theorem cyclicModel_eq_of_primitive {m : ℕ} (hm : 0 < m) {ω ν : ℂˣ}
    (hω : IsPrimitiveRoot ω m) (hν : IsPrimitiveRoot ν m) :
    cyclicModel ω = cyclicModel ν := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have he : Subgroup.zpowers ω⁻¹ = Subgroup.zpowers ν⁻¹ :=
    hω.inv.zpowers_eq.trans hν.inv.zpowers_eq.symm
  have hmap := congrArg (fun K : Subgroup ℂˣ => K.map torusHom) he
  simpa only [MonoidHom.map_zpowers, cyclicModel, cyclicGenerator_eq_torus] using hmap

theorem dihedralModel_eq_of_primitive {m : ℕ} (hm : 0 < m) {ω ν : ℂˣ}
    (hω : IsPrimitiveRoot ω m) (hν : IsPrimitiveRoot ν m) :
    dihedralModel ω = dihedralModel ν := by
  have he := cyclicModel_eq_of_primitive hm hω hν
  ext q
  change (q ∈ cyclicModel ω ∨ ∃ r ∈ cyclicModel ω, q = xClass * r) ↔
    (q ∈ cyclicModel ν ∨ ∃ r ∈ cyclicModel ν, q = xClass * r)
  rw [he]

theorem cyclicModel_isCyclic (ω : ℂˣ) : IsCyclic (cyclicModel ω) := by
  change IsCyclic (Subgroup.zpowers (cyclicGenerator ω))
  infer_instance

theorem dihedralModel_not_isCyclic {m : ℕ} (hm : 2 ≤ m) {ω : ℂˣ}
    (hω : IsPrimitiveRoot ω m) : ¬ IsCyclic (dihedralModel ω) := by
  obtain ⟨e⟩ := dihedralModel_isomorphism hω
  intro hc
  have h := DihedralGroup.isCyclic_iff.mp (e.isCyclic.mpr hc)
  omega

/-- A coarse bound suffices to separate the three Platonic models from the
cyclic and dihedral models of equal cardinality. -/
theorem modelPGL_order_le_five (p : PlatonicModel) (x : modelPGL p) :
    orderOf x ≤ 5 := by
  cases p with
  | tetrahedral =>
      have ho := a4_orders_exhaustive (tetrahedral_iso_A4 x)
      rw [tetrahedral_iso_A4.orderOf_eq] at ho
      rcases ho with h | h | h <;> omega
  | octahedral =>
      have ho := s4_orders_exhaustive (octahedral_iso_S4 x)
      rw [octahedral_iso_S4.orderOf_eq] at ho
      rcases ho with h | h | h | h <;> omega
  | icosahedral =>
      have ho := a5_orders_exhaustive (icosahedral_iso_A5 x)
      rw [icosahedral_iso_A5.orderOf_eq] at ho
      rcases ho with h | h | h | h <;> omega

theorem modelPGL_card_ge_twelve (p : PlatonicModel) : 12 ≤ Nat.card (modelPGL p) := by
  rw [modelPGL_card]
  cases p <;> norm_num [size]

theorem modelPGL_not_isCyclic (p : PlatonicModel) : ¬ IsCyclic (modelPGL p) := by
  intro hc
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hc
  have hbound := modelPGL_order_le_five p x
  have hcard := modelPGL_card_ge_twelve p
  omega

theorem platonic_eq_of_card_eq {p q : PlatonicModel}
    (h : Nat.card (modelPGL p) = Nat.card (modelPGL q)) : p = q := by
  rw [modelPGL_card, modelPGL_card] at h
  cases p <;> cases q <;> simp_all [size]

/-- Every displayed dihedral model has an actual element of rotation order m. -/
theorem dihedralModel_exists_order {m : ℕ} {ω : ℂˣ} (hω : IsPrimitiveRoot ω m) :
    ∃ x : dihedralModel ω, orderOf x = m := by
  obtain ⟨e⟩ := dihedralModel_isomorphism hω
  exact ⟨e (DihedralGroup.r 1),
    (e.orderOf_eq _).trans DihedralGroup.orderOf_r_one⟩

theorem dihedralModel_not_mulEquiv_platonic {m : ℕ} {ω : ℂˣ}
    (hω : IsPrimitiveRoot ω m) (p : PlatonicModel) :
    ¬ Nonempty (dihedralModel ω ≃* modelPGL p) := by
  rintro ⟨e⟩
  have hc : 2 * m = Nat.card (modelPGL p) :=
    (dihedralModel_card hω).symm.trans (Nat.card_congr e.toEquiv)
  have hlarge := modelPGL_card_ge_twelve p
  obtain ⟨x, hx⟩ := dihedralModel_exists_order hω
  have hsmall := modelPGL_order_le_five p (e x)
  rw [e.orderOf_eq, hx] at hsmall
  omega

theorem cyclicModel_not_mulEquiv_dihedral (ω : ℂˣ) {m : ℕ} (hm : 2 ≤ m)
    {ν : ℂˣ} (hν : IsPrimitiveRoot ν m) :
    ¬ Nonempty (cyclicModel ω ≃* dihedralModel ν) := by
  rintro ⟨e⟩
  exact dihedralModel_not_isCyclic hm hν (e.isCyclic.mp (cyclicModel_isCyclic ω))

theorem cyclicModel_not_mulEquiv_platonic (ω : ℂˣ) (p : PlatonicModel) :
    ¬ Nonempty (cyclicModel ω ≃* modelPGL p) := by
  rintro ⟨e⟩
  exact modelPGL_not_isCyclic p (e.isCyclic.mp (cyclicModel_isCyclic ω))

end
end Holant.LocalDrafts.FinitePGL2
