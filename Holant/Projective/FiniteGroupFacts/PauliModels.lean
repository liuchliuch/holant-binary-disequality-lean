import Holant.Projective.FiniteGroupFacts.ActualModels
import Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
import Holant.Projective.FiniteGroupFacts.PlatonicStructure

/-! The literal Pauli subgroup inside all three displayed Platonic models. -/

namespace Holant.Projective.FiniteGroupFacts

open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Projective.BoundedTorsion ProjectiveCentralizers

noncomputable section
set_option backward.isDefEq.respectTransparency false

def axisIndex (g : PlatonicModel) (i : Fin 4) : Fin (size g) :=
  ⟨i.val, by cases g <;> simp only [size] <;> omega⟩

theorem representative_axis (g : PlatonicModel) (i : Fin 4) :
    representative g (axisIndex g i) = quaternionBasis i := by
  have hr : raw g (axisIndex g i) =
      fun j => if j = i then GoldenInt.ofInt 1 else GoldenInt.zero := by
    cases g <;> fin_cases i <;> ext j <;> fin_cases j <;> rfl
  rw [representative, hr, goldenMatrix_axis]

theorem indexed_axis_zero (g : PlatonicModel) :
    (indexedPGL g (axisIndex g 0) : PGL2 ℂ) = 1 := by
  change pglMk ℂ (representativeGL g _) = pglMk ℂ 1
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨1, one_ne_zero, ?_⟩
  change representative g (axisIndex g 0) = _
  rw [representative_axis]
  ext i j
  cases i <;> cases j <;> simp [quaternionBasis, Q0, Holant.Signature.equality]

theorem indexed_axis_one (g : PlatonicModel) :
    (indexedPGL g (axisIndex g 1) : PGL2 ℂ) = xClass := by
  change pglMk ℂ (representativeGL g _) = pglMk ℂ xGL
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
  change representative g (axisIndex g 1) = _
  rw [representative_axis]
  ext i j
  cases i <;> cases j <;> simp [quaternionBasis, Q1, xGL, antidiagonalGL, antidiagonal]

theorem indexed_axis_two (g : PlatonicModel) :
    (indexedPGL g (axisIndex g 2) : PGL2 ℂ) = xClass * zClass := by
  change pglMk ℂ (representativeGL g _) = pglMk ℂ xGL * pglMk ℂ zGL
  rw [← map_mul]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ?_⟩
  change representative g (axisIndex g 2) = _
  rw [representative_axis]
  ext i j
  cases i <;> cases j <;>
    simp [quaternionBasis, Q2, xGL, zGL, diagonalGL, diagonal,
      antidiagonalGL, antidiagonal, Matrix.mul_apply]

theorem indexed_axis_three (g : PlatonicModel) :
    (indexedPGL g (axisIndex g 3) : PGL2 ℂ) = zClass := by
  change pglMk ℂ (representativeGL g _) = pglMk ℂ zGL
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
  change representative g (axisIndex g 3) = _
  rw [representative_axis]
  ext i j
  cases i <;> cases j <;> simp [quaternionBasis, Q3, zGL, diagonalGL, diagonal]

theorem pauli_le_model (g : PlatonicModel) : pauliSubgroup ≤ modelPGL g := by
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl
  · rw [← indexed_axis_one g]
    exact (indexedPGL g (axisIndex g 1)).property
  · rw [← indexed_axis_three g]
    exact (indexedPGL g (axisIndex g 3)).property

/-- The Pauli subgroup is exactly the four quaternion-axis projective classes. -/
theorem pauli_eq_axis_range (g : PlatonicModel) :
    (pauliSubgroup : Set (PGL2 ℂ)) =
      Set.range (fun i : Fin 4 => (indexedPGL g (axisIndex g i) : PGL2 ℂ)) := by
  ext q
  change q ∈ pauliSubgroup ↔ _
  rw [pauli_membership]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, indexed_axis_zero g⟩
    · exact ⟨1, indexed_axis_one g⟩
    · exact ⟨3, indexed_axis_three g⟩
    · exact ⟨2, indexed_axis_two g⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl (indexed_axis_zero g)
    · exact Or.inr (Or.inl (indexed_axis_one g))
    · exact Or.inr (Or.inr (Or.inr (indexed_axis_two g)))
    · exact Or.inr (Or.inr (Or.inl (indexed_axis_three g)))

theorem indexed_mem_pauli_iff (g : PlatonicModel) (i : Fin (size g)) :
    (indexedPGL g i : PGL2 ℂ) ∈ pauliSubgroup ↔ i.val < 4 := by
  change (indexedPGL g i : PGL2 ℂ) ∈ (pauliSubgroup : Set (PGL2 ℂ)) ↔ _
  rw [pauli_eq_axis_range g]
  constructor
  · rintro ⟨j, hj⟩
    have hij := indexedPGL_injective g (Subtype.ext hj)
    have hv := congrArg Fin.val hij
    change j.val = i.val at hv
    omega
  · intro hi
    refine ⟨⟨i.val, hi⟩, ?_⟩
    have he : axisIndex g ⟨i.val, hi⟩ = i := Fin.ext rfl
    exact congrArg (fun j => (indexedPGL g j : PGL2 ℂ)) he

theorem octahedral_iso_indexed (i : Fin 24) :
    octahedral_iso_S4 (indexedPGL .octahedral i) = fourPermutation i := by
  change indexSymmetricEquiv ((indexPGLEquiv .octahedral).symm
    (indexPGLEquiv .octahedral i)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem tetrahedral_iso_indexed (i : Fin 12) :
    tetrahedral_iso_A4 (indexedPGL .tetrahedral i) = tetrahedralAlternatingAction i := by
  change indexTetrahedralEquiv ((indexPGLEquiv .tetrahedral).symm
    (indexPGLEquiv .tetrahedral i)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The literal four-point permutation action sends quaternion axes to the normal V₄. -/
theorem fourPermutation_mem_kleinFour (i : Fin 24) :
    fourPermutation i ∈ s4KleinFour ↔ i.val < 4 := by
  rw [s4_mem_kleinFour]
  revert i
  decide +kernel

theorem tetrahedralAction_mem_kleinFour (i : Fin 12) :
    tetrahedralAlternatingAction i ∈ a4KleinFour ↔ i.val < 4 := by
  rw [a4_mem_kleinFour]
  revert i
  decide +kernel

/-- The usual normal V₄ of S₄ pulls back to the actual Pauli subgroup of O. -/
theorem octahedral_pauli_preimage :
    s4KleinFour.comap octahedral_iso_S4.toMonoidHom =
      pauliSubgroup.subgroupOf (modelPGL .octahedral) := by
  ext q
  obtain ⟨i, rfl⟩ := indexedPGL_surjective .octahedral q
  change octahedral_iso_S4 (indexedPGL .octahedral i) ∈ s4KleinFour ↔
    (indexedPGL .octahedral i : PGL2 ℂ) ∈ pauliSubgroup
  rw [octahedral_iso_indexed, fourPermutation_mem_kleinFour, indexed_mem_pauli_iff]

/-- The normal V₄ of A₄ pulls back to the same actual Pauli subgroup of T. -/
theorem tetrahedral_pauli_preimage :
    a4KleinFour.comap tetrahedral_iso_A4.toMonoidHom =
      pauliSubgroup.subgroupOf (modelPGL .tetrahedral) := by
  ext q
  obtain ⟨i, rfl⟩ := indexedPGL_surjective .tetrahedral q
  change tetrahedral_iso_A4 (indexedPGL .tetrahedral i) ∈ a4KleinFour ↔
    (indexedPGL .tetrahedral i : PGL2 ℂ) ∈ pauliSubgroup
  rw [tetrahedral_iso_indexed, tetrahedralAction_mem_kleinFour, indexed_mem_pauli_iff]

instance octahedral_pauli_normal :
    (pauliSubgroup.subgroupOf (modelPGL .octahedral)).Normal := by
  rw [← octahedral_pauli_preimage]
  let _ : s4KleinFour.Normal := s4_kleinFour_normal
  infer_instance

instance tetrahedral_pauli_normal :
    (pauliSubgroup.subgroupOf (modelPGL .tetrahedral)).Normal := by
  rw [← tetrahedral_pauli_preimage]
  let _ : a4KleinFour.Normal := a4_kleinFour_normal
  infer_instance

end
end Holant.Projective.FiniteGroupFacts
