import Holant.Projective.FiniteGroupFacts.PauliModels
import Holant.Projective.FiniteGroupFacts.NormalizerSupport
import Holant.Projective.FiniteGroupFacts.ModelInclusions

/-! The full Pauli normalizer and the T/O normalizer equalities in the actual
PGL₂ quotient. Finite conjugation transitivity is transported through the
proved literal octahedral action. -/
namespace Holant.Projective.FiniteGroupFacts
open Holant.Projective.BoundedTorsion ProjectiveCentralizers
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem pauli_x_ne_one : xClass ≠ 1 := antidiagonal_ne_one 1 1

theorem pauli_z_ne_one : zClass ≠ 1 := by
  intro h
  have ho := zClass_involution
  simp [h] at ho

theorem pauli_x_ne_z : xClass ≠ zClass := by
  intro h
  exact (Set.disjoint_left.mp diagonal_antidiagonal_disjoint)
    (show zClass ∈ diagonalClasses from ⟨1, -1, rfl⟩)
    (show zClass ∈ antidiagonalClasses from ⟨1, 1, h.symm⟩)

theorem octahedral_pauli_double (q : modelPGL .octahedral)
    (hq : (q : PGL2 ℂ) ∈ pauliSubgroup) (hne : (q : PGL2 ℂ) ≠ 1) :
    DoubleTransposition (octahedral_iso_S4 q) := by
  have hm : octahedral_iso_S4 q ∈ s4KleinFour := by
    change q ∈ s4KleinFour.comap octahedral_iso_S4.toMonoidHom
    rw [octahedral_pauli_preimage]
    exact hq
  rcases (s4_mem_kleinFour _).mp hm with h | h
  · have he : q = 1 := octahedral_iso_S4.injective (by simpa using h)
    exact False.elim (hne (congrArg Subtype.val he))
  · exact h

theorem octahedral_realizes_pauli_conjugation (n : PGL2 ℂ)
    (hn : n ∈ Subgroup.normalizer (pauliSubgroup : Set (PGL2 ℂ))) :
    ∃ a ∈ modelPGL .octahedral,
      a * xClass * a⁻¹ = n * xClass * n⁻¹ ∧
      a * zClass * a⁻¹ = n * zClass * n⁻¹ := by
  let x : modelPGL .octahedral := ⟨xClass, pauli_le_model _ xClass_mem_pauli⟩
  let z : modelPGL .octahedral := ⟨zClass, pauli_le_model _ zClass_mem_pauli⟩
  have hnx : n * xClass * n⁻¹ ∈ pauliSubgroup := (hn xClass).mp xClass_mem_pauli
  have hnz : n * zClass * n⁻¹ ∈ pauliSubgroup := (hn zClass).mp zClass_mem_pauli
  let nx : modelPGL .octahedral := ⟨n * xClass * n⁻¹, pauli_le_model _ hnx⟩
  let nz : modelPGL .octahedral := ⟨n * zClass * n⁻¹, pauli_le_model _ hnz⟩
  have hnx1 : (nx : PGL2 ℂ) ≠ 1 := by
    intro h
    apply pauli_x_ne_one
    exact (MulAut.conj n).injective (by simpa [nx] using h)
  have hnz1 : (nz : PGL2 ℂ) ≠ 1 := by
    intro h
    apply pauli_z_ne_one
    exact (MulAut.conj n).injective (by simpa [nz] using h)
  have hxz : octahedral_iso_S4 x ≠ octahedral_iso_S4 z := by
    intro h
    exact pauli_x_ne_z (congrArg Subtype.val (octahedral_iso_S4.injective h))
  have hnxz : octahedral_iso_S4 nx ≠ octahedral_iso_S4 nz := by
    intro h
    have he := congrArg Subtype.val (octahedral_iso_S4.injective h)
    exact pauli_x_ne_z ((MulAut.conj n).injective he)
  obtain ⟨c, hx, hz⟩ := s4_double_pairs_transitive
    (octahedral_iso_S4 x) (octahedral_iso_S4 z)
    (octahedral_iso_S4 nx) (octahedral_iso_S4 nz)
    (octahedral_pauli_double x xClass_mem_pauli pauli_x_ne_one)
    (octahedral_pauli_double z zClass_mem_pauli pauli_z_ne_one) hxz
    (octahedral_pauli_double nx hnx hnx1) (octahedral_pauli_double nz hnz hnz1) hnxz
  let a := octahedral_iso_S4.symm c
  have hax : a * x * a⁻¹ = nx := by
    apply octahedral_iso_S4.injective
    simpa [a] using hx
  have haz : a * z * a⁻¹ = nz := by
    apply octahedral_iso_S4.injective
    simpa [a] using hz
  exact ⟨a, a.property, congrArg Subtype.val hax, congrArg Subtype.val haz⟩

theorem pauli_normalizer :
    Subgroup.normalizer (pauliSubgroup : Set (PGL2 ℂ)) = modelPGL .octahedral := by
  apply normalizer_eq_of_generator_action xClass zClass
  · exact pauli_le_model _
  · exact pauli_self_centralizer
  · change modelPGL .octahedral ≤ Subgroup.normalizer (pauliSubgroup : Set (PGL2 ℂ))
    exact Subgroup.le_normalizer_of_normal_subgroupOf (pauli_le_model _)
  · exact octahedral_realizes_pauli_conjugation

theorem tetrahedral_pauli_characteristic :
    (pauliSubgroup.subgroupOf (modelPGL .tetrahedral)).Characteristic := by
  rw [← tetrahedral_pauli_preimage]
  have : a4KleinFour.Characteristic := alternatingGroup.characteristic_kleinFour (by simp)
  exact characteristic_comap_equiv tetrahedral_iso_A4 a4KleinFour

theorem octahedral_pauli_characteristic :
    (pauliSubgroup.subgroupOf (modelPGL .octahedral)).Characteristic := by
  rw [← octahedral_pauli_preimage]
  have : s4KleinFour.Characteristic := s4_kleinFour_characteristic
  exact characteristic_comap_equiv octahedral_iso_S4 s4KleinFour

/-- Source Lemma 2.2(vii), first normalizer equality. -/
theorem tetrahedral_normalizer :
    Subgroup.normalizer (modelPGL .tetrahedral : Set (PGL2 ℂ)) = modelPGL .octahedral := by
  have := tetrahedral_pauli_characteristic
  have h := normalizer_le_of_characteristic pauliSubgroup (modelPGL .tetrahedral) (pauli_le_model _)
  rw [pauli_normalizer] at h
  exact le_antisymm h octahedral_le_normalizer_tetrahedral

/-- Source Lemma 2.2(vii), second normalizer equality. -/
theorem octahedral_normalizer :
    Subgroup.normalizer (modelPGL .octahedral : Set (PGL2 ℂ)) = modelPGL .octahedral := by
  have := octahedral_pauli_characteristic
  have h := normalizer_le_of_characteristic pauliSubgroup (modelPGL .octahedral) (pauli_le_model _)
  rw [pauli_normalizer] at h
  exact le_antisymm h (modelPGL .octahedral).le_normalizer

end
end Holant.Projective.FiniteGroupFacts
