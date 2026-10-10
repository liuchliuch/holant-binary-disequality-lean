import Holant.Projective.FiniteGroupFacts.FourPointAction
import Holant.Projective.BoundedTorsion.PGL
import Holant.Certificates.MatchingProductBridge.GroupInverses
import Holant.Certificates.PlatonicBridgeInterface.FivePointAction

/-! Literal T/O/I as subgroups of the genuine quotient PGL₂(ℂ).
The finite indices are proved bijective onto those subgroups and their products
are proved to be the actual quotient products before any abstract identification. -/
namespace Holant.Projective.FiniteGroupFacts
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure (ProjectiveMatrixGroup)
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev ComplexMatrix := Matrix Bool Bool ℂ
abbrev ComplexGL := Matrix.GeneralLinearGroup Bool ℂ

theorem model_projectiveMatrixGroup (g : PlatonicModel) :
    ProjectiveMatrixGroup {U : ComplexMatrix | groupDirection g U} where
  one_mem := by
    rw [← representative_identity g]
    exact representative_mem _ _
  mul_mem := fun _ hU _ hV => groupDirection_mul g hU hV
  inverse_mem := by
    intro U hU
    have hd := isUnit_iff_ne_zero.mpr (groupDirection_det_ne_zero g hU)
    exact ⟨U⁻¹, groupDirection_inverse g hU, Matrix.mul_nonsing_inv U hd,
      Matrix.nonsing_inv_mul U hd⟩
  scalar_mem := fun _ hU _ hc => groupDirection_smul g hU hc

/-- The actual subgroup of the quotient, rather than a transported group on indices. -/
def modelPGL (g : PlatonicModel) : Subgroup (PGL2 ℂ) :=
  projectiveSubgroup (model_projectiveMatrixGroup g)

def representativeGL (g : PlatonicModel) (i : Fin (size g)) : ComplexGL :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (representative g i) (representative_det_ne_zero g i)

def indexedPGL (g : PlatonicModel) (i : Fin (size g)) : modelPGL g :=
  ⟨pglMk ℂ (representativeGL g i), representativeGL g i, representative_mem g i, rfl⟩

theorem indexedPGL_injective (g : PlatonicModel) : Function.Injective (indexedPGL g) := by
  intro i j h
  have he := pglMk_eq_iff_projectiveClass_eq.mp (congrArg Subtype.val h)
  obtain ⟨c, hc, he⟩ := projectiveClass_eq_iff.mp he
  exact projectively_injective g i j c he

theorem indexedPGL_surjective (g : PlatonicModel) : Function.Surjective (indexedPGL g) := by
  rintro ⟨q, U, hU, rfl⟩
  obtain ⟨i, c, hc, he⟩ := (complete g U).mp hU
  refine ⟨i, Subtype.ext ?_⟩
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  exact (projectiveClass_eq_iff.mpr ⟨c, hc, he⟩).symm

def indexPGLEquiv (g : PlatonicModel) : Fin (size g) ≃ modelPGL g :=
  Equiv.ofBijective (indexedPGL g) ⟨indexedPGL_injective g, indexedPGL_surjective g⟩

instance (g : PlatonicModel) : Fintype (modelPGL g) := Fintype.ofEquiv _ (indexPGLEquiv g)

theorem modelPGL_card (g : PlatonicModel) : Nat.card (modelPGL g) = size g := by
  rw [Nat.card_congr (indexPGLEquiv g).symm, Nat.card_fin]

/-- This equation explicitly identifies the actual quotient group law with the
preexisting scalar-checked matrix multiplication certificates. -/
theorem indexedPGL_product (g : PlatonicModel) (i j : Fin (size g)) :
    indexedPGL g i * indexedPGL g j = indexedPGL g (productIndex g i j) := by
  apply Subtype.ext
  change pglMk ℂ (representativeGL g i) * pglMk ℂ (representativeGL g j) = _
  rw [← map_mul]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  exact projectiveClass_eq_iff.mpr
    ⟨productScale g i j, Int.cast_ne_zero.mpr (raw_certificate g i j).1, mul_exact g i j⟩

@[simp] theorem indexedPGL_identity (g : PlatonicModel) :
    indexedPGL g (identityIndex g) = 1 := by
  apply Subtype.ext
  change pglMk ℂ (representativeGL g _) = pglMk ℂ 1
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  change projectiveClass (representative g _) = projectiveClass (1 : ComplexMatrix)
  rw [representative_identity]

/-- The saturated literal source family and quotient subgroup agree on every GL representative. -/
theorem pglMk_mem_model_iff (g : PlatonicModel) (U : ComplexGL) :
    pglMk ℂ U ∈ modelPGL g ↔ groupDirection g (U : ComplexMatrix) := by
  constructor
  · rintro ⟨V, hV, hVU⟩
    obtain ⟨c, hc, he⟩ := projectiveClass_eq_iff.mp
      (pglMk_eq_iff_projectiveClass_eq.mp hVU.symm)
    rw [he]
    exact groupDirection_smul g hV hc
  · intro hU
    exact ⟨U, hU, rfl⟩

/-- The actual octahedral subgroup is S₄. -/
def octahedral_iso_S4 : modelPGL .octahedral ≃* S4 where
  toEquiv := (indexPGLEquiv .octahedral).symm.trans indexSymmetricEquiv
  map_mul' := by
    intro a b
    obtain ⟨i, rfl⟩ := indexedPGL_surjective .octahedral a
    obtain ⟨j, rfl⟩ := indexedPGL_surjective .octahedral b
    rw [indexedPGL_product]
    change indexSymmetricEquiv ((indexPGLEquiv .octahedral).symm (indexPGLEquiv .octahedral _)) =
      indexSymmetricEquiv ((indexPGLEquiv .octahedral).symm (indexPGLEquiv .octahedral _)) *
      indexSymmetricEquiv ((indexPGLEquiv .octahedral).symm (indexPGLEquiv .octahedral _))
    simp only [Equiv.symm_apply_apply]
    exact fourPermutation_product i j

/-- The actual tetrahedral subgroup is A₄. -/
def tetrahedral_iso_A4 : modelPGL .tetrahedral ≃* A4 where
  toEquiv := (indexPGLEquiv .tetrahedral).symm.trans indexTetrahedralEquiv
  map_mul' := by
    intro a b
    obtain ⟨i, rfl⟩ := indexedPGL_surjective .tetrahedral a
    obtain ⟨j, rfl⟩ := indexedPGL_surjective .tetrahedral b
    rw [indexedPGL_product]
    change indexTetrahedralEquiv ((indexPGLEquiv .tetrahedral).symm (indexPGLEquiv .tetrahedral _)) =
      indexTetrahedralEquiv ((indexPGLEquiv .tetrahedral).symm (indexPGLEquiv .tetrahedral _)) *
      indexTetrahedralEquiv ((indexPGLEquiv .tetrahedral).symm (indexPGLEquiv .tetrahedral _))
    simp only [Equiv.symm_apply_apply]
    exact tetrahedralAlternatingAction_product i j

/-- The previous literal five-point action identifies the actual quotient subgroup with A₅. -/
def icosahedral_iso_A5 : modelPGL .icosahedral ≃* A5 where
  toEquiv := (indexPGLEquiv .icosahedral).symm.trans
    Holant.Certificates.PlatonicBridgeInterface.indexAlternatingEquiv
  map_mul' := by
    intro a b
    obtain ⟨i, rfl⟩ := indexedPGL_surjective .icosahedral a
    obtain ⟨j, rfl⟩ := indexedPGL_surjective .icosahedral b
    rw [indexedPGL_product]
    change Holant.Certificates.PlatonicBridgeInterface.indexAlternatingEquiv
      ((indexPGLEquiv .icosahedral).symm (indexPGLEquiv .icosahedral _)) =
      Holant.Certificates.PlatonicBridgeInterface.indexAlternatingEquiv
        ((indexPGLEquiv .icosahedral).symm (indexPGLEquiv .icosahedral _)) *
      Holant.Certificates.PlatonicBridgeInterface.indexAlternatingEquiv
        ((indexPGLEquiv .icosahedral).symm (indexPGLEquiv .icosahedral _))
    simp only [Equiv.symm_apply_apply]
    exact Holant.Certificates.PlatonicBridgeInterface.indexAlternatingEquiv_product i j

end
end Holant.Projective.FiniteGroupFacts
