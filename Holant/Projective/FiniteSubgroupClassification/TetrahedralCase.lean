import Holant.Projective.FiniteSubgroupClassification.NormalKlein
import Holant.Projective.FiniteSubgroupClassification.Signatures
import Holant.Projective.FiniteSubgroupClassification.FixedPoints

/-! The tetrahedral case of the finite projective subgroup classification,
using the action on a genuine four-point orbit of the complex projective line. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
noncomputable section

/-- An orbit containing more than two projective points carries a faithful
restricted action of a finite projective subgroup. -/
theorem faithfulSMul_orbit_of_two_lt_ncard
    (H : Subgroup (PGL2 ℂ)) [Finite H] (p : ProjectiveLine)
    (hp : 2 < (MulAction.orbit H p).ncard) :
    FaithfulSMul H (MulAction.orbit H p) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  apply Subtype.ext
  by_contra hne
  have hfin : IsOfFinOrder (g : PGL2 ℂ) :=
    H.subtype.isOfFinOrder (isOfFinOrder_of_finite g)
  have hsub : MulAction.orbit H p ⊆ fixedPoints (g : PGL2 ℂ) := by
    intro q hq
    exact congrArg Subtype.val (hg ⟨q, hq⟩)
  have hle := Set.ncard_le_ncard hsub (fixedPoints_finite hfin hne)
  rw [fixedPoints_ncard hfin hne] at hle
  omega

/-- Labeling a genuine four-point orbit embeds its finite projective group
into the actual symmetric group on four letters. -/
theorem exists_injective_hom_S4_of_orbit_four
    (H : Subgroup (PGL2 ℂ)) [Finite H] (p : ProjectiveLine)
    (hp : (MulAction.orbit H p).ncard = 4) :
    ∃ f : H →* S4, Function.Injective f := by
  letI : FaithfulSMul H (MulAction.orbit H p) :=
    faithfulSMul_orbit_of_two_lt_ncard H p (by omega)
  have hc : Nat.card (MulAction.orbit H p) = 4 := by
    simpa only [Nat.card_coe_set_eq] using hp
  let e : MulAction.orbit H p ≃ Fin 4 :=
    (Nat.equivFinOfCardPos (by omega)).trans (finCongr hc)
  refine ⟨e.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom H (MulAction.orbit H p)), ?_⟩
  exact e.permCongrHom.injective.comp MulAction.toPerm_injective

/-- An order-twelve projective group acting on a four-point orbit is
isomorphic to the actual alternating subgroup of `S4`. -/
theorem nonempty_mulEquiv_A4_of_card_twelve_orbit_four
    (H : Subgroup (PGL2 ℂ)) (hcard : Nat.card H = 12)
    (p : ProjectiveLine) (hp : (MulAction.orbit H p).ncard = 4) :
    Nonempty (H ≃* A4) := by
  letI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨f, hf⟩ := exists_injective_hom_S4_of_orbit_four H p hp
  have hrange : Nat.card f.range = 12 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hcard
  have hindex : f.range.index = 2 := by
    have he := f.range.index_mul_card
    rw [hrange] at he
    have hS4 : Nat.card S4 = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      norm_num [Nat.factorial]
    rw [hS4] at he
    omega
  exact ⟨(MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (s4_unique_index_two f.range hindex))⟩

/-- A projective group isomorphic to `A4` contains an actual normal Klein
four subgroup in the ambient scalar quotient. -/
theorem exists_normal_klein_of_mulEquiv_A4
    (H : Subgroup (PGL2 ℂ)) (e : H ≃* A4) :
    ∃ K : Subgroup (PGL2 ℂ), K ≤ H ∧ IsKleinFour K ∧ (K.subgroupOf H).Normal := by
  letI : IsKleinFour a4KleinFour := a4_kleinFour_isKleinFour
  letI : a4KleinFour.Normal := a4_kleinFour_normal
  let S : Subgroup H := a4KleinFour.map e.symm.toMonoidHom
  letI : IsKleinFour S :=
    kleinFour_of_mulEquiv
      (Subgroup.equivMapOfInjective a4KleinFour e.symm.toMonoidHom e.symm.injective).symm
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

/-- Orbit-stabilizer turns a point stabilizer of order three inside an
order-twelve group into the genuine four-point orbit required above. -/
theorem orbit_ncard_four_of_card_twelve_stabilizer_three
    (H : Subgroup (PGL2 ℂ)) (hcard : Nat.card H = 12)
    (p : ProjectiveLine) (hp : Nat.card (MulAction.stabilizer H p) = 3) :
    (MulAction.orbit H p).ncard = 4 := by
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H p)
  rw [Nat.card_prod, Nat.card_coe_set_eq, hp, hcard] at he
  omega

/-- The normal Klein subgroup follows from the actual order-twelve,
four-point-orbit hypotheses, without assuming a finite-group classification. -/
theorem exists_normal_klein_of_card_twelve_orbit_four
    (H : Subgroup (PGL2 ℂ)) (hcard : Nat.card H = 12)
    (p : ProjectiveLine) (hp : (MulAction.orbit H p).ncard = 4) :
    ∃ K : Subgroup (PGL2 ℂ), K ≤ H ∧ IsKleinFour K ∧ (K.subgroupOf H).Normal := by
  obtain ⟨e⟩ := nonempty_mulEquiv_A4_of_card_twelve_orbit_four H hcard p hp
  exact exists_normal_klein_of_mulEquiv_A4 H e

/-- The tetrahedral branch: an actual projective subgroup of order twelve
with a genuine four-point orbit is conjugate to the displayed matrix model. -/
theorem card_twelve_orbit_four_conjugacy
    (H : Subgroup (PGL2 ℂ)) (hcard : Nat.card H = 12)
    (p : ProjectiveLine) (hp : (MulAction.orbit H p).ncard = 4) :
    ∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom = modelPGL .tetrahedral := by
  obtain ⟨K, hKH, hK, hnormal⟩ :=
    exists_normal_klein_of_card_twelve_orbit_four H hcard p hp
  letI : IsKleinFour K := hK
  letI : (K.subgroupOf H).Normal := hnormal
  exact normal_klein_card_twelve_conjugacy H K hKH hcard

/-- Equivalent tetrahedral input in point-stabilizer form. -/
theorem card_twelve_stabilizer_three_conjugacy
    (H : Subgroup (PGL2 ℂ)) (hcard : Nat.card H = 12)
    (p : ProjectiveLine) (hp : Nat.card (MulAction.stabilizer H p) = 3) :
    ∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom = modelPGL .tetrahedral :=
  card_twelve_orbit_four_conjugacy H hcard p
    (orbit_ncard_four_of_card_twelve_stabilizer_three H hcard p hp)

/-- The actual `(2,3,3)` exceptional-orbit branch of the source incidence
argument has the displayed tetrahedral conjugacy conclusion. The order and
order-three stabilizer are exactly the facts supplied by the signature. -/
theorem exceptional_233_conjugacy
    (H : Subgroup (PGL2 ℂ)) (e : Fin 3 ≃ ExceptionalOrbits H)
    (_ha : stabilizerOrder H (e 0) = 2)
    (hb : stabilizerOrder H (e 1) = 3)
    (_hc : stabilizerOrder H (e 2) = 3) (hcard : Nat.card H = 12) :
    ∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom = modelPGL .tetrahedral := by
  apply card_twelve_stabilizer_three_conjugacy H hcard (e 1).out.val
  simpa only [stabilizerOrder, exceptional_stabilizer_eq] using hb

end
end Holant.Projective.FiniteSubgroupClassification
