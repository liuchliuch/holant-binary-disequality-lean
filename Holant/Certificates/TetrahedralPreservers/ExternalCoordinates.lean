import Holant.Certificates.TetrahedralPreservers.RankOneClassification

/-! The literal plus-sign R_ext from the manuscript. The older external
dictionary uses the inverse rotation; the explicit permutation below proves
that the two rotations give the same projective set. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence
open Holant.Certificates.OctahedralSeparator
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def theta : End :=
  ![![1,0,0,0],![0,1,0,0],![0,0,rootTwo/2,-rootTwo/2],![0,0,rootTwo/2,rootTwo/2]]

def thetaInv : End :=
  ![![1,0,0,0],![0,1,0,0],![0,0,rootTwo/2,rootTwo/2],![0,0,-rootTwo/2,rootTwo/2]]

theorem theta_inverses : theta * thetaInv = 1 ∧ thetaInv * theta = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [theta,thetaInv,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply] <;>
    ring_nf <;> simp [rootTwo_sq]

@[simp] theorem theta_sharp : sharp theta = theta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sharp_apply,theta,frobeniusSigns] <;> ring

@[simp] theorem thetaInv_sharp : sharp thetaInv = thetaInv := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sharp_apply,thetaInv,frobeniusSigns] <;> ring

def sourceRRaw : OctahedralSeparator.Mat := q 0 + ms (root-1) (q 1)
def sourceRInvRaw : OctahedralSeparator.Mat :=
  mat (coeff (1/2) (1/4) 0 0) (coeff 0 0 0 (-1/4))
    (coeff 0 0 0 (-1/4)) (coeff (1/2) (1/4) 0 0)

theorem sourceR_inverses_raw :
    mm sourceRRaw sourceRInvRaw = q 0 ∧ mm sourceRInvRaw sourceRRaw = q 0 := by
  decide +kernel

def sourceR : BinaryMatrix := complexMatrix sourceRRaw
def sourceRInv : BinaryMatrix := complexMatrix sourceRInvRaw

/-- Exactly R_ext = Q0 + (sqrt(2)-1) Q1, including the manuscript's sign. -/
theorem sourceR_literal : sourceR = Matrix.of Q0 + ((Real.sqrt 2 : ℂ)-1) • Matrix.of Q1 := by
  simp [sourceR,sourceRRaw,complexMatrix_q,quaternionBasis,embed_sub,embed_one,root,embed_coeff,rootTwo]

theorem sourceRInv_eq_inv : sourceRInv = sourceR⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  change complexMatrix sourceRRaw * complexMatrix sourceRInvRaw = 1
  rw [← complexMatrix_mm,sourceR_inverses_raw.1,complexMatrix_q0]

def sourceTheta (K : BinaryMatrix) : BinaryMatrix := sourceRInv * (K * sourceR)
def sourcePull (K : BinaryMatrix) : BinaryMatrix := sourceR * (K * sourceRInv)

theorem sourceTheta_literal (K : BinaryMatrix) :
    sourceTheta K = sourceR⁻¹ * K * sourceR := by
  rw [sourceTheta,sourceRInv_eq_inv,Matrix.mul_assoc]

theorem sourceTheta_coordinates (r : V) : coordinates (sourceTheta (assemble r)) = theta *ᵥ r := by
  ext i
  fin_cases i <;>
    simp [coordinates_apply,quaternionCoefficient,sourceTheta,sourceR,sourceRInv,
      sourceRRaw,sourceRInvRaw,complexMatrix,Matrix.mul_apply,mm,q,ms,mat,
      embed_add,embed_sub,embed_mul,embed_coeff,embed_one,embed_zero,embed_imag,
      root,assemble,Q0,Q1,Q2,Q3,Holant.Signature.equality,theta,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq,rootTwo_sq] <;> ring

theorem sourcePull_coordinates (r : V) : coordinates (sourcePull (assemble r)) = thetaInv *ᵥ r := by
  ext i
  fin_cases i <;>
    simp [coordinates_apply,quaternionCoefficient,sourcePull,sourceR,sourceRInv,
      sourceRRaw,sourceRInvRaw,complexMatrix,Matrix.mul_apply,mm,q,ms,mat,
      embed_add,embed_sub,embed_mul,embed_coeff,embed_one,embed_zero,embed_imag,
      root,assemble,Q0,Q1,Q2,Q3,Holant.Signature.equality,thetaInv,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq,rootTwo_sq] <;> ring

def sourceIndex : Fin 12 → Fin 12 := ![0,1,3,2,6,4,7,5,10,8,11,9]
def sourceIndexInv : Fin 12 → Fin 12 := ![0,1,3,2,5,7,4,6,9,11,8,10]
def sourceScale (k : Fin 12) : Scalar := if k=3 then -1 else 1

theorem sourceIndex_right_inverse : ∀ k, sourceIndex (sourceIndexInv k)=k := by decide +kernel
theorem sourceScale_ne_zero : ∀ k, sourceScale k ≠ 0 := by decide +kernel

theorem sourceTheta_rows : ∀ k : Fin 12,
    mm sourceRInvRaw (mm (standard (RainbowOrbit.External.firstTwelve k)) sourceRRaw) =
      ms (sourceScale k) (RainbowOrbit.External.raw (sourceIndex k)) := by
  intro k
  fin_cases k <;> decide +kernel

theorem sourcePull_rows : ∀ k : Fin 12,
    mm sourceRRaw (mm (standard (RainbowOrbit.External.firstTwelve k)) sourceRInvRaw) =
      RainbowOrbit.External.raw k := by
  intro k
  fin_cases k <;> decide +kernel

theorem standard_representative_complex (k : Fin 12) :
    RainbowOrbit.representative .tetrahedral k =
      complexMatrix (standard (RainbowOrbit.External.firstTwelve k)) := by
  rw [← RainbowOrbit.octahedralRaw_standard,RainbowOrbit.External.tetrahedral_restriction]
  rfl

theorem theta_standardPoint (k : Fin 12) :
    theta *ᵥ standardPoint k = embed (sourceScale k) • externalPoint (sourceIndex k) := by
  rw [← sourceTheta_coordinates]
  change coordinates (sourceTheta (assemble (quaternionCoefficient _))) = _
  rw [assemble_coefficient,standard_representative_complex]
  unfold sourceTheta sourceR sourceRInv
  rw [← complexMatrix_mm,← complexMatrix_mm,sourceTheta_rows,complexMatrix_ms,map_smul]
  rfl

theorem thetaInv_standardPoint (k : Fin 12) : thetaInv *ᵥ standardPoint k = externalPoint k := by
  rw [← sourcePull_coordinates]
  change coordinates (sourcePull (assemble (quaternionCoefficient _))) = _
  rw [assemble_coefficient,standard_representative_complex]
  unfold sourcePull sourceR sourceRInv
  rw [← complexMatrix_mm,← complexMatrix_mm,sourcePull_rows]
  rfl

theorem thetaInv_externalPoint (k : Fin 12) :
    thetaInv *ᵥ externalPoint k =
      (embed (sourceScale (sourceIndexInv k)))⁻¹ • standardPoint (sourceIndexInv k) := by
  have h := theta_standardPoint (sourceIndexInv k)
  rw [sourceIndex_right_inverse] at h
  have hh := congrArg (fun r : V => thetaInv *ᵥ r) h
  rw [Matrix.mulVec_mulVec,theta_inverses.2,Matrix.one_mulVec,Matrix.mulVec_smul] at hh
  rw [hh,smul_smul,inv_mul_cancel₀ (embed_ne_zero (sourceScale_ne_zero _)),one_smul]

theorem theta_externalPoint (k : Fin 12) : theta *ᵥ externalPoint k = standardPoint k := by
  rw [← thetaInv_standardPoint,Matrix.mulVec_mulVec,theta_inverses.1,Matrix.one_mulVec]

theorem theta_standard_external {r : V} (h : r ∈ Standard) : theta *ᵥ r ∈ External := by
  obtain ⟨k,c,hc,rfl⟩ := (standard_iff r).mp h
  rw [Matrix.mulVec_smul,theta_standardPoint]
  exact external_saturated (external_saturated (externalPoint_mem _)
    (embed_ne_zero (sourceScale_ne_zero _))) hc

theorem thetaInv_standard_external {r : V} (h : r ∈ Standard) : thetaInv *ᵥ r ∈ External := by
  obtain ⟨k,c,hc,rfl⟩ := (standard_iff r).mp h
  rw [Matrix.mulVec_smul,thetaInv_standardPoint]
  exact external_saturated (externalPoint_mem _) hc

theorem theta_external_standard {r : V} (h : r ∈ External) : theta *ᵥ r ∈ Standard := by
  obtain ⟨k,c,hc,rfl⟩ := (external_iff r).mp h
  rw [Matrix.mulVec_smul,theta_externalPoint]
  exact standard_saturated (standardPoint_mem _) hc

theorem thetaInv_external_standard {r : V} (h : r ∈ External) : thetaInv *ᵥ r ∈ Standard := by
  obtain ⟨k,c,hc,rfl⟩ := (external_iff r).mp h
  rw [Matrix.mulVec_smul,thetaInv_externalPoint]
  exact standard_saturated (standard_saturated (standardPoint_mem _)
    (inv_ne_zero (embed_ne_zero (sourceScale_ne_zero _)))) hc

/-- The square normalizes the full standard coefficient set, in both directions. -/
theorem theta_square_standard (r : V) : (theta * theta) *ᵥ r ∈ Standard ↔ r ∈ Standard := by
  constructor
  · intro h
    have hh := thetaInv_external_standard (thetaInv_standard_external h)
    have hi : thetaInv * (thetaInv * (theta * theta)) = 1 := by
      rw [← Matrix.mul_assoc thetaInv theta theta,theta_inverses.2,
        Matrix.one_mul,theta_inverses.2]
    simpa only [Matrix.mulVec_mulVec,Matrix.mul_assoc,hi,Matrix.one_mulVec] using hh
  · intro h
    rw [← Matrix.mulVec_mulVec]
    exact theta_external_standard (theta_standard_external h)

end Holant.Certificates.TetrahedralPreservers
