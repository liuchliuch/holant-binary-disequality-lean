import Holant.Certificates.PlatonicBridgeInterface.OctahedralCounts
import Holant.Certificates.OctahedralSeparator.CardMap

/-! The manuscript's actual theta/coefficient dictionary for all four marked
forms, as invertible complex-linear maps. These are coefficient identities only. -/
namespace Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.TetrahedralBridge (quaternionCoefficient_add quaternionCoefficient_smul quaternionCoefficient_basis basis_expansion)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

abbrev Form := Holant.Certificates.OctahedralSeparator.Form

/-- A genuine basis equivalence, retaining the four literal quaternion kernels. -/
def quaternionCoordinates : Binary ≃ₗ[ℂ] (Fin 4 → ℂ) where
  toFun U := quaternionCoefficient U
  invFun z := ∑ k : Fin 4, z k • quaternionBasis k
  left_inv U := (basis_expansion U).symm
  right_inv z := by
    funext k
    fin_cases k <;>
      norm_num [quaternionCoefficient,Fin.sum_univ_succ,quaternionBasis,
        Pi.add_apply,Pi.smul_apply,smul_eq_mul,Q0,Q1,Q2,Q3,Signature.equality] <;>
      ring_nf <;> norm_num [Complex.I_sq] <;> ring
  map_add' U V := by funext k; exact quaternionCoefficient_add U V k
  map_smul' c U := by funext k; exact quaternionCoefficient_smul c U k

def quaternionBasis' : Module.Basis (Fin 4) ℂ Binary := Module.Basis.ofEquivFun quaternionCoordinates

theorem quaternionBasis'_apply (k : Fin 4) : quaternionBasis' k = quaternionBasis k := by
  rw [quaternionBasis',Module.Basis.coe_ofEquivFun]
  change (∑ j : Fin 4, (Pi.single (M := fun _ : Fin 4 => ℂ) k 1) j • quaternionBasis j) = _
  simp

def wordEquiv : Fin 16 ≃ (Fin 4 → Bool) := Equiv.ofBijective TetrahedralDeck.words
  ⟨by decide +kernel,TetrahedralDeck.words_surjective⟩

def tensorCoordinates : FourTensor ≃ₗ[ℂ] (Fin 16 → ℂ) where
  toFun W := fun j => W (wordEquiv j)
  invFun z := fun x => z (wordEquiv.symm x)
  left_inv W := by funext x; simp
  right_inv z := by funext j; simp
  map_add' W V := rfl
  map_smul' c W := rfl

def tensorBasis : Module.Basis (Fin 16) ℂ FourTensor := Module.Basis.ofEquivFun tensorCoordinates

/-- The source card matrix rank is the intrinsic dimension of the actual map's range. -/
theorem mapRank_eq_finrank (Φ : Binary →ₗ[ℂ] FourTensor) :
    mapRank Φ = Module.finrank ℂ (LinearMap.range Φ) := by
  have he : (show Matrix (Fin 16) (Fin 4) ℂ from fun row k =>
      Φ (quaternionBasis k) (TetrahedralDeck.words row)) =
      LinearMap.toMatrix quaternionBasis' tensorBasis Φ := by
    ext row k
    simp only [LinearMap.toMatrix_apply,quaternionBasis'_apply,tensorBasis,
      Module.Basis.ofEquivFun_repr_apply]
    rfl
  unfold mapRank
  rw [he,Matrix.rank_eq_finrank_range_toLin _ tensorBasis quaternionBasis',Matrix.toLin_toMatrix]

open Holant.Certificates.OctahedralSeparator (Mat Scalar complexMatrix complexTensor)

def inverseCoefficientLegs (f : Form) : Fin 4 → Mat :=
  ![Holant.Certificates.OctahedralSeparator.conjugator f,
    Holant.Certificates.OctahedralSeparator.mt (Holant.Certificates.OctahedralSeparator.inverseConjugator f),
    Holant.Certificates.OctahedralSeparator.conjugator f,
    Holant.Certificates.OctahedralSeparator.mt (Holant.Certificates.OctahedralSeparator.inverseConjugator f)]

theorem coefficient_legs_inverse : ∀ f : Form, ∀ j : Fin 4,
    Holant.Certificates.OctahedralSeparator.mm (inverseCoefficientLegs f j)
      (Holant.Certificates.OctahedralSeparator.coefficientLegs f j) = Holant.Certificates.OctahedralSeparator.q 0 ∧
    Holant.Certificates.OctahedralSeparator.mm (Holant.Certificates.OctahedralSeparator.coefficientLegs f j)
      (inverseCoefficientLegs f j) = Holant.Certificates.OctahedralSeparator.q 0 := by decide +kernel

theorem kernel_mul_complex (U V : Mat) :
    Kernel.mul (complexMatrix U) (complexMatrix V) =
      complexMatrix (Holant.Certificates.OctahedralSeparator.mm U V) := by
  rw [Holant.Certificates.OctahedralSeparator.complexMatrix_mm]
  ext a b
  simp [Kernel.mul,Matrix.mul_apply]

/-- L in the manuscript's normalized card dictionary. -/
def coefficientEquiv (f : Form) : FourTensor ≃ₗ[ℂ] FourTensor where
  toFun W := Signature.coordinateAction
    (fun j => complexMatrix (Holant.Certificates.OctahedralSeparator.coefficientLegs f j)) W
  invFun W := Signature.coordinateAction (fun j => complexMatrix (inverseCoefficientLegs f j)) W
  left_inv W := by
    apply Signature.coordinateAction_cancel
    intro j
    rw [kernel_mul_complex,(coefficient_legs_inverse f j).1,
      Holant.Certificates.OctahedralSeparator.complexMatrix_q0]
    rfl
  right_inv W := by
    apply Signature.coordinateAction_cancel
    intro j
    rw [kernel_mul_complex,(coefficient_legs_inverse f j).2,
      Holant.Certificates.OctahedralSeparator.complexMatrix_q0]
    rfl
  map_add' := Signature.coordinateAction_add _
  map_smul' c W := by
    funext x
    simp [Signature.coordinateAction,smul_eq_mul,Finset.mul_sum]
    congr 1
    funext y
    ring

/-- Theta is the literal current-form conjugation, including the mixed forms. -/
def thetaEquiv (f : Form) : Binary ≃ₗ[ℂ] Binary where
  toFun := Holant.Certificates.OctahedralSeparator.complexTheta f
  invFun := Holant.Certificates.OctahedralSeparator.complexPull f
  left_inv := Holant.Certificates.OctahedralSeparator.complexPull_complexTheta f
  right_inv := Holant.Certificates.OctahedralSeparator.complexTheta_complexPull f
  map_add' U V := by
    ext a b
    simp [Holant.Certificates.OctahedralSeparator.complexTheta,Matrix.mul_apply,
      Finset.sum_add_distrib,mul_add,add_mul]
  map_smul' c U := Holant.Certificates.OctahedralSeparator.complexTheta_smul f c U

/-- The source's physical coefficient map is L composed with Phi composed with theta inverse. -/
def markMap (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor) : Binary →ₗ[ℂ] FourTensor :=
  (coefficientEquiv f).toLinearMap.comp (Φ.comp (thetaEquiv f).symm.toLinearMap)

def unmarkMap (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor) : Binary →ₗ[ℂ] FourTensor :=
  (coefficientEquiv f).symm.toLinearMap.comp (Φ.comp (thetaEquiv f).toLinearMap)

@[simp] theorem unmark_mark (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor) : unmarkMap f (markMap f Φ) = Φ := by
  ext U x
  simp [unmarkMap,markMap]

@[simp] theorem mark_unmark (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor) : markMap f (unmarkMap f Φ) = Φ := by
  ext U x
  simp [unmarkMap,markMap]

theorem markMap_injective (f : Form) : Function.Injective (markMap f) :=
  Function.LeftInverse.injective (unmark_mark f)

@[simp] theorem markMap_theta (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor) (K : Binary) :
    markMap f Φ (thetaEquiv f K) = coefficientEquiv f (Φ K) := by simp [markMap]

theorem markMap_rank (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor) :
    mapRank (markMap f Φ) = mapRank Φ := by
  rw [mapRank_eq_finrank,mapRank_eq_finrank]
  unfold markMap
  rw [LinearMap.range_comp,LinearEquiv.finrank_map_eq,
    LinearMap.range_comp_of_range_eq_top _ (thetaEquiv f).symm.range]

end
end Holant.Certificates.PlatonicBridgeInterface.Octahedral
