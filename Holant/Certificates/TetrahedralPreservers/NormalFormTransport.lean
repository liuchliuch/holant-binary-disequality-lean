import Holant.Certificates.TetrahedralPreservers.ExternalTransport
import Holant.Certificates.TetrahedralPreservers.Reconstruction

/-! Analytic transport and original-tensor reconstruction of the two full-rank
normal forms. This does not assume or claim that all full-rank preservers have
already been classified into those forms. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence
open Holant.Certificates.OctahedralSeparator
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

theorem matrix_ext_action {A B : End} (h : ∀ r : V, A *ᵥ r = B *ᵥ r) : A=B := by
  ext i j
  simpa using congrFun (h (Pi.single j 1)) i

theorem sandwich_action (U W : BinaryMatrix) (r : V) :
    sandwich U W *ᵥ r = coordinates (U * assemble r * W) := by
  ext i
  fin_cases i <;>
    simp [sandwich,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,coordinates_apply,
      quaternionCoefficient,quaternionBasis,assemble,Q0,Q1,Q2,Q3,
      Holant.Signature.equality,Matrix.mul_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem transposeSandwich_action (U W : BinaryMatrix) (r : V) :
    transposeSandwich U W *ᵥ r = coordinates (U * (assemble r).transpose * W) := by
  ext i
  fin_cases i <;>
    simp [transposeSandwich,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,coordinates_apply,
      quaternionCoefficient,quaternionBasis,assemble,Q0,Q1,Q2,Q3,
      Holant.Signature.equality,Matrix.mul_apply,Matrix.transpose_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem assemble_theta (r : V) : assemble (theta *ᵥ r) = sourceTheta (assemble r) := by
  apply coordinates.injective
  change quaternionCoefficient (assemble (theta *ᵥ r)) = _
  rw [coefficient_assemble,sourceTheta_coordinates]

theorem assemble_thetaInv (r : V) : assemble (thetaInv *ᵥ r) = sourcePull (assemble r) := by
  apply coordinates.injective
  change quaternionCoefficient (assemble (thetaInv *ᵥ r)) = _
  rw [coefficient_assemble,sourcePull_coordinates]

theorem sourceR_symmetric : sourceR.transpose=sourceR := by
  have h : mt sourceRRaw=sourceRRaw := by decide +kernel
  exact (complexMatrix_mt sourceRRaw).symm.trans (congrArg complexMatrix h)

theorem sourceRInv_symmetric : sourceRInv.transpose=sourceRInv := by
  have h : mt sourceRInvRaw=sourceRInvRaw := by decide +kernel
  exact (complexMatrix_mt sourceRInvRaw).symm.trans (congrArg complexMatrix h)

theorem sourceR_inverses : sourceR*sourceRInv=1 ∧ sourceRInv*sourceR=1 := by
  constructor
  · change complexMatrix sourceRRaw * complexMatrix sourceRInvRaw=1
    rw [← complexMatrix_mm,sourceR_inverses_raw.1,complexMatrix_q0]
  · change complexMatrix sourceRInvRaw * complexMatrix sourceRRaw=1
    rw [← complexMatrix_mm,sourceR_inverses_raw.2,complexMatrix_q0]

theorem toExternal_sandwich (U W : BinaryMatrix) :
    toExternal (sandwich U W) = sandwich (sourceTheta U) (sourceTheta W) := by
  apply matrix_ext_action
  intro r
  simp only [toExternal,← Matrix.mulVec_mulVec,sandwich_action]
  rw [← sourceTheta_coordinates]
  change coordinates (sourceTheta (assemble (quaternionCoefficient _))) = _
  rw [assemble_coefficient,assemble_thetaInv]
  simp only [sourceTheta,sourcePull,Matrix.mul_assoc]

theorem toExternal_transposeSandwich (U W : BinaryMatrix) :
    toExternal (transposeSandwich U W) =
      transposeSandwich (sourceRInv*U*sourceRInv) (sourceR*W*sourceR) := by
  apply matrix_ext_action
  intro r
  simp only [toExternal,← Matrix.mulVec_mulVec,transposeSandwich_action]
  rw [← sourceTheta_coordinates]
  change coordinates (sourceTheta (assemble (quaternionCoefficient _))) = _
  rw [assemble_coefficient,assemble_thetaInv]
  simp only [sourceTheta,sourcePull,Matrix.transpose_mul,sourceR_symmetric,
    sourceRInv_symmetric,Matrix.mul_assoc]

/-- These are exactly the two extra R_ext factors in the manuscript's
transpose normal form, with all matrix products retained. -/
theorem transpose_left_factor (U : BinaryMatrix) :
    sourceRInv*U*sourceRInv = sourceTheta U * (sourceRInv*sourceRInv) := by
  simp only [sourceTheta,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc sourceR sourceRInv sourceRInv,sourceR_inverses.1,Matrix.one_mul]

theorem transpose_right_factor (W : BinaryMatrix) :
    sourceR*W*sourceR = (sourceR*sourceR)*sourceTheta W := by
  simp only [sourceTheta,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc sourceR sourceRInv,sourceR_inverses.1,Matrix.one_mul]

theorem reconstruct_toExternal_sandwich (U W : BinaryMatrix) :
    reconstruct (toExternal (sandwich U W)) =
      P1 (sourceTheta U).transpose (sourceTheta W) := by
  rw [toExternal_sandwich,reconstruct_sandwich]

theorem reconstruct_toExternal_transposeSandwich (U W : BinaryMatrix) :
    reconstruct (toExternal (transposeSandwich U W)) =
      P2 ((sourceR*sourceR)*sourceTheta W)
        (sourceTheta U*(sourceRInv*sourceRInv)).transpose := by
  rw [toExternal_transposeSandwich,reconstruct_transposeSandwich,
    transpose_left_factor,transpose_right_factor]

theorem sourceR_dets : sourceR.det ≠ 0 ∧ sourceRInv.det ≠ 0 := by
  have h := congrArg Matrix.det sourceR_inverses.1
  simp only [Matrix.det_mul,Matrix.det_one] at h
  constructor <;> intro hn <;> simp [hn] at h

theorem sourceTheta_det_ne_zero {U : BinaryMatrix} (hU : U.det ≠ 0) :
    (sourceTheta U).det ≠ 0 := by
  simpa only [sourceTheta,Matrix.det_mul] using
    mul_ne_zero sourceR_dets.2 (mul_ne_zero hU sourceR_dets.1)

/-- The crossing factors stay nonsingular in the actual external coordinates. -/
theorem external_crossing_factors {U W : BinaryMatrix} (hU : U.det ≠ 0) (hW : W.det ≠ 0) :
    (sourceTheta U).transpose.det ≠ 0 ∧ (sourceTheta W).det ≠ 0 ∧
    ((sourceR*sourceR)*sourceTheta W).det ≠ 0 ∧
    (sourceTheta U*(sourceRInv*sourceRInv)).transpose.det ≠ 0 := by
  have hTU := sourceTheta_det_ne_zero hU
  have hTW := sourceTheta_det_ne_zero hW
  simp only [Matrix.det_transpose,Matrix.det_mul]
  exact ⟨hTU,hTW,mul_ne_zero (mul_ne_zero sourceR_dets.1 sourceR_dets.1) hTW,
    mul_ne_zero hTU (mul_ne_zero sourceR_dets.2 sourceR_dets.2)⟩

end Holant.Certificates.TetrahedralPreservers
