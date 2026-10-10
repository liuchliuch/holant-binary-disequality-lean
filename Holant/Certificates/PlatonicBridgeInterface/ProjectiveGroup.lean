import Holant.Certificates.PlatonicBridgeInterface.FivePointAction
import Holant.Certificates.RainbowOrbit.GroupRepresentatives
import Holant.Certificates.MatchingProductBridge.GroupInverses
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Algebra.Group.TransferInstance

/-! The sixty actual complex projective matrix classes, with the multiplication
induced by matrix multiplication, are isomorphic to the alternating group A5. -/
namespace Holant.Certificates.PlatonicBridgeInterface
open Holant.Certificates.RainbowOrbit Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev MatrixPoint := Projectivization ℂ (Matrix Bool Bool ℂ)

def displayedPoint (i : Fin 60) : MatrixPoint :=
  Projectivization.mk ℂ (representative .icosahedral i) (representative_ne_zero _ _)

theorem displayedPoint_injective : Function.Injective displayedPoint := by
  intro i j h
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  exact projectively_injective .icosahedral i j c hc.symm

/-- This carrier consists of projective points of actual complex matrices,
not integers standing in for otherwise unidentified group elements. -/
def ProjectiveClass := {p : MatrixPoint // p ∈ Set.range displayedPoint}

def indexedClass (i : Fin 60) : ProjectiveClass := ⟨displayedPoint i, i, rfl⟩

theorem indexedClass_bijective : Function.Bijective indexedClass := by
  constructor
  · intro i j h
    exact displayedPoint_injective (congrArg Subtype.val h)
  · rintro ⟨p,i,hi⟩
    exact ⟨i, Subtype.ext hi⟩

def indexClassEquiv : Fin 60 ≃ ProjectiveClass :=
  Equiv.ofBijective indexedClass indexedClass_bijective

def classAlternatingEquiv : ProjectiveClass ≃ alternatingGroup (Fin 5) :=
  indexClassEquiv.symm.trans indexAlternatingEquiv

instance : Group ProjectiveClass := classAlternatingEquiv.group
instance : Fintype ProjectiveClass := Fintype.ofEquiv (Fin 60) indexClassEquiv

def projective_iso_A5 : ProjectiveClass ≃* alternatingGroup (Fin 5) :=
  classAlternatingEquiv.mulEquiv

theorem projective_card_sixty : Fintype.card ProjectiveClass = 60 := by
  rw [Fintype.card_congr indexClassEquiv.symm, Fintype.card_fin]

@[simp] theorem classAlternatingEquiv_indexed (i : Fin 60) :
    classAlternatingEquiv (indexedClass i) = indexAlternatingEquiv i := by
  change indexAlternatingEquiv (indexClassEquiv.symm (indexClassEquiv i)) = _
  rw [Equiv.symm_apply_apply]

/-- The transported group operation is exactly the previously verified
projective multiplication table, not an unrelated group structure. -/
theorem indexedClass_mul (i j : Fin 60) :
    indexedClass i * indexedClass j = indexedClass (icosahedralProductIndex i j) := by
  apply projective_iso_A5.injective
  rw [map_mul]
  change classAlternatingEquiv (indexedClass i) * classAlternatingEquiv (indexedClass j) =
    classAlternatingEquiv (indexedClass (icosahedralProductIndex i j))
  simp only [classAlternatingEquiv_indexed]
  exact (indexAlternatingEquiv_product i j).symm

/-- Exact matrix multiplication with its nonzero representative scalar. -/
theorem induced_multiplication (i j : Fin 60) :
    (indexedClass i * indexedClass j).val =
      Projectivization.mk ℂ (representative .icosahedral i * representative .icosahedral j)
        (by
          intro h
          have hd := mul_ne_zero (representative_det_ne_zero .icosahedral i)
            (representative_det_ne_zero .icosahedral j)
          rw [←Matrix.det_mul, h, Matrix.det_zero] at hd
          exact hd rfl) := by
  rw [indexedClass_mul]
  apply Eq.symm
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨(productScale .icosahedral i j : ℂ), (mul_exact .icosahedral i j).symm⟩

theorem matrix_nonzero {U : Matrix Bool Bool ℂ} (hU : groupDirection .icosahedral U) : U ≠ 0 := by
  intro h
  have hd := groupDirection_det_ne_zero .icosahedral hU
  change U.det ≠ 0 at hd
  rw [h, Matrix.det_zero] at hd
  exact hd rfl

def matrixClass (U : Matrix Bool Bool ℂ) (hU : groupDirection .icosahedral U) : ProjectiveClass := by
  refine ⟨Projectivization.mk ℂ U (matrix_nonzero hU), ?_⟩
  obtain ⟨i,c,hc,he⟩ := (complete .icosahedral U).mp hU
  refine ⟨i, ?_⟩
  apply Eq.symm
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,he.symm⟩

theorem matrixClass_scaled (i : Fin 60) (c : ℂ) (hc : c ≠ 0)
    (hU : groupDirection .icosahedral (c • representative .icosahedral i)) :
    matrixClass (c • representative .icosahedral i) hU = indexedClass i := by
  apply Subtype.ext
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,rfl⟩

/-- Matrix multiplication induces the group law for arbitrary nonzero complex
representatives, including all rescalings of the sixty displayed classes. -/
theorem matrixClass_mul (U V : Matrix Bool Bool ℂ)
    (hU : groupDirection .icosahedral U) (hV : groupDirection .icosahedral V) :
    matrixClass (U*V) (groupDirection_mul .icosahedral hU hV) =
      matrixClass U hU * matrixClass V hV := by
  obtain ⟨i,c,hc,rfl⟩ := (complete .icosahedral U).mp hU
  obtain ⟨j,d,hd,rfl⟩ := (complete .icosahedral V).mp hV
  rw [matrixClass_scaled i c hc, matrixClass_scaled j d hd, indexedClass_mul]
  apply Subtype.ext
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨c*d*(productScale .icosahedral i j : ℂ), ?_⟩
  rw [Matrix.smul_mul, Matrix.mul_smul, mul_exact]
  simp [smul_smul, mul_assoc, productIndex]

theorem projective_closed_operations (U V : Matrix Bool Bool ℂ)
    (hU : groupDirection .icosahedral U) (hV : groupDirection .icosahedral V) :
    groupDirection .icosahedral (U*V) ∧
      groupDirection .icosahedral (U⁻¹ : Matrix Bool Bool ℂ) ∧ groupDirection .icosahedral U.transpose :=
  ⟨groupDirection_mul .icosahedral hU hV,
    groupDirection_inverse .icosahedral hU, groupDirection_transpose .icosahedral hU⟩


theorem indexedClass_zero : indexedClass 0 = 1 := by
  apply projective_iso_A5.injective
  rw [map_one]
  change classAlternatingEquiv (indexedClass 0) = 1
  rw [classAlternatingEquiv_indexed]
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact five_action_identity x

theorem matrixClass_one (h1 : groupDirection .icosahedral (1 : Matrix Bool Bool ℂ)) :
    matrixClass 1 h1 = 1 := by
  rw [←indexedClass_zero]
  apply Subtype.ext
  change Projectivization.mk ℂ 1 _ = Projectivization.mk ℂ (representative .icosahedral (0 : Fin 60)) _
  congr 1
  exact (representative_identity .icosahedral).symm

/-- Inversion in the projective group is induced by the actual matrix inverse. -/
theorem matrixClass_inverse (U : Matrix Bool Bool ℂ) (hU : groupDirection .icosahedral U) :
    matrixClass U⁻¹ (groupDirection_inverse .icosahedral hU) = (matrixClass U hU)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←matrixClass_mul]
  have hu := Matrix.nonsing_inv_mul U (isUnit_iff_ne_zero.mpr
    (groupDirection_det_ne_zero .icosahedral hU))
  simp only [hu]
  exact matrixClass_one _

end
end Holant.Certificates.PlatonicBridgeInterface
