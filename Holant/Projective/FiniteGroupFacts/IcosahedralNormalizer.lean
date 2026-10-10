import Holant.Projective.FiniteGroupFacts.PauliModels
import Holant.Projective.FiniteGroupFacts.ModelInclusions
import Holant.Projective.FiniteGroupFacts.Normalizers
import Holant.Projective.FiniteGroupFacts.GoldenNormalizerWitness

/-! The normalizer of the literal icosahedral subgroup in genuine complex PGL₂. -/

namespace Holant.Projective.FiniteGroupFacts

open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Projective.BoundedTorsion ProjectiveCentralizers

noncomputable section
set_option backward.isDefEq.respectTransparency false

def icosahedralX : modelPGL .icosahedral :=
  ⟨xClass, pauli_le_model .icosahedral xClass_mem_pauli⟩

theorem icosahedralX_order : orderOf icosahedralX = 2 := by
  simpa [icosahedralX] using xClass_involution

/-- The centralizer of the displayed involution inside I is exactly its Pauli V₄. -/
theorem icosahedral_centralizer_x :
    Subgroup.centralizer ({icosahedralX} : Set (modelPGL .icosahedral)) =
      pauliSubgroup.subgroupOf (modelPGL .icosahedral) := by
  let C := Subgroup.centralizer ({icosahedralX} : Set (modelPGL .icosahedral))
  let e := icosahedral_iso_A5
  let D := Subgroup.centralizer ({e icosahedralX} : Set A5)
  let f : C → D := fun q => ⟨e q, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (Subgroup.mem_centralizer_singleton_iff.mp q.property))⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val h
  have hD : Nat.card D = 4 := by
    apply a5_involution_centralizer_card
    rw [involution_iff_orderOf, MulEquiv.orderOf_eq]
    exact icosahedralX_order
  have hC : Nat.card C ≤ 4 := (Nat.card_le_card_of_injective f hf).trans_eq hD
  have hP : Nat.card (pauliSubgroup.subgroupOf (modelPGL .icosahedral)) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pauli_le_model .icosahedral)).toEquiv]
    exact pauli_card
  apply (Subgroup.eq_of_le_of_card_ge (H := pauliSubgroup.subgroupOf (modelPGL .icosahedral))
    (K := C) ?_ ?_).symm
  · intro q hq
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact ((commute_x_z_iff q).mpr ((pauli_membership q).mp hq)).1.eq
  · rw [hP]
    exact hC

theorem icosahedral_inf_centralizer_x :
    modelPGL .icosahedral ⊓ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)) =
      pauliSubgroup := by
  ext q
  constructor
  · rintro ⟨hI, hx⟩
    have hm : (⟨q, hI⟩ : modelPGL .icosahedral) ∈
        Subgroup.centralizer ({icosahedralX} : Set (modelPGL .icosahedral)) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [icosahedral_centralizer_x] at hm
    exact hm
  · intro hp
    exact ⟨pauli_le_model .icosahedral hp,
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((commute_x_z_iff q).mpr ((pauli_membership q).mp hp)).1.eq⟩

/-- An element normalizing I and centralizing X necessarily normalizes the Pauli subgroup. -/
theorem normalizes_pauli_of_normalizes_icosahedral_commutes_x {n : PGL2 ℂ}
    (hn : n ∈ Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ)))
    (hx : Commute n xClass) :
    n ∈ Subgroup.normalizer (pauliSubgroup : Set (PGL2 ℂ)) := by
  have hc : n ∈ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hx.eq
  have hnc := (Subgroup.centralizer ({xClass} : Set (PGL2 ℂ))).le_normalizer hc
  rw [← icosahedral_inf_centralizer_x]
  intro q
  exact and_congr (hn q) (hnc q)

/-- Every conjugate of X induced by a normalizer element is already conjugate to X inside I. -/
theorem icosahedral_internal_conjugate_x {n : PGL2 ℂ}
    (hn : n ∈ Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ))) :
    ∃ i : modelPGL .icosahedral,
      (i : PGL2 ℂ) * xClass * (i : PGL2 ℂ)⁻¹ = n * xClass * n⁻¹ := by
  let y : modelPGL .icosahedral :=
    ⟨n * xClass * n⁻¹, (hn xClass).mp (pauli_le_model .icosahedral xClass_mem_pauli)⟩
  let e := icosahedral_iso_A5
  have hy : orderOf y = 2 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf ((MulAut.conj n) xClass) = 2
    rw [MulEquiv.orderOf_eq]
    exact xClass_involution
  have hxA : Involution (e icosahedralX) := by
    rw [involution_iff_orderOf, MulEquiv.orderOf_eq]
    exact icosahedralX_order
  have hyA : Involution (e y) := by
    rw [involution_iff_orderOf, MulEquiv.orderOf_eq]
    exact hy
  obtain ⟨c, hc⟩ := isConj_iff.mp (a5_involutions_one_class _ _ hxA hyA)
  refine ⟨e.symm c, ?_⟩
  have hi : e.symm c * icosahedralX * (e.symm c)⁻¹ = y := by
    apply e.injective
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hc
  exact congrArg Subtype.val hi

/-- The index-two inclusion T ≤ O turns one explicit excluded coset representative
into the complete intersection calculation. -/
theorem octahedral_inf_icosahedral_normalizer_of_witness
    (hw : (indexedPGL .octahedral (12 : Fin 24) : PGL2 ℂ) ∉
      Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ))) :
    modelPGL .octahedral ⊓
      Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ)) = modelPGL .tetrahedral := by
  let H := (modelPGL .tetrahedral).subgroupOf (modelPGL .octahedral)
  let N := Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ))
  have hwH : indexedPGL .octahedral (12 : Fin 24) ∉ H := fun h =>
    hw (tetrahedral_le_normalizer_icosahedral h)
  apply le_antisymm
  · rintro q ⟨hqO, hqN⟩
    by_contra hqT
    let qO : modelPGL .octahedral := ⟨q, hqO⟩
    have hqH : qO ∉ H := hqT
    have hprod : qO * indexedPGL .octahedral (12 : Fin 24) ∈ H := by
      apply (H.mul_mem_iff_of_index_two tetrahedral_index_in_octahedral).mpr
      simp only [hqH, hwH]
    have hprodN : q * (indexedPGL .octahedral (12 : Fin 24) : PGL2 ℂ) ∈ N :=
      tetrahedral_le_normalizer_icosahedral hprod
    have hwN := N.mul_mem (N.inv_mem hqN) hprodN
    exact hw (by simpa only [← mul_assoc, inv_mul_cancel, one_mul] using hwN)
  · exact fun q hq => ⟨tetrahedral_le_octahedral hq,
      tetrahedral_le_normalizer_icosahedral hq⟩

/-- Reduction of N(I)=I to the separately computed Pauli normalizer and O intersection. -/
theorem icosahedral_normalizer_of_pauli_and_intersection
    (hP : Subgroup.normalizer (pauliSubgroup : Set (PGL2 ℂ)) = modelPGL .octahedral)
    (hO : modelPGL .octahedral ⊓
      Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ)) = modelPGL .tetrahedral) :
    Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ)) = modelPGL .icosahedral := by
  apply le_antisymm
  · intro n hn
    obtain ⟨i, hi⟩ := icosahedral_internal_conjugate_x hn
    let m : PGL2 ℂ := (i : PGL2 ℂ)⁻¹ * n
    let N := Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ))
    have hmN : m ∈ N := N.mul_mem
      (N.inv_mem ((modelPGL .icosahedral).le_normalizer i.property)) hn
    have hconj : m * xClass * m⁻¹ = xClass := by
      calc
        m * xClass * m⁻¹ = (i : PGL2 ℂ)⁻¹ * (n * xClass * n⁻¹) * i := by
          dsimp [m]
          group
        _ = (i : PGL2 ℂ)⁻¹ * ((i : PGL2 ℂ) * xClass * (i : PGL2 ℂ)⁻¹) * i := by
          rw [hi]
        _ = xClass := by group
    have hmx : Commute m xClass := mul_inv_eq_iff_eq_mul.mp hconj
    have hmP := normalizes_pauli_of_normalizes_icosahedral_commutes_x hmN hmx
    have hmO : m ∈ modelPGL .octahedral := hP ▸ hmP
    have hmT : m ∈ modelPGL .tetrahedral := hO ▸ (show m ∈
        modelPGL .octahedral ⊓ N from ⟨hmO, hmN⟩)
    have hmem := (modelPGL .icosahedral).mul_mem i.property (tetrahedral_le_icosahedral hmT)
    simpa [m, mul_assoc] using hmem
  · exact (modelPGL .icosahedral).le_normalizer

theorem octahedral_inf_icosahedral_normalizer :
    modelPGL .octahedral ⊓
      Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ)) = modelPGL .tetrahedral :=
  octahedral_inf_icosahedral_normalizer_of_witness
    octahedral_twelve_not_normalizer_icosahedral

/-- Source Lemma 2.2(7): the actual icosahedral model is self-normalizing in PGL₂(ℂ). -/
theorem icosahedral_normalizer :
    Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ)) = modelPGL .icosahedral :=
  icosahedral_normalizer_of_pauli_and_intersection pauli_normalizer
    octahedral_inf_icosahedral_normalizer

end
end Holant.Projective.FiniteGroupFacts
