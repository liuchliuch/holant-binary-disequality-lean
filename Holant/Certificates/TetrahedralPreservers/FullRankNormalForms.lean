import Holant.Certificates.TetrahedralPreservers.FullRankCount
import Holant.Certificates.TetrahedralPreservers.NormalFormRaw
import Holant.Certificates.TetrahedralPreservers.NormalFormTransport

/-! Every rank-four preserver, with no normal-form hypothesis, has the two
matrix forms in the source and reconstructs the actual binary-pair tensor. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

def qMatrix (p : ZV) : BinaryMatrix := assemble (liftVector p)

theorem qMatrix_conjugate (p : ZV) :
    qMatrix p * qMatrix (zConj p) = (zNorm p : ℂ) • (1 : BinaryMatrix) := by
  ext a b
  cases a <;> cases b <;>
    simp [qMatrix,assemble,liftVector,zConj,zNorm,Matrix.mul_apply,Q0,Q1,Q2,Q3,
      Holant.Signature.equality,Matrix.one_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem qMatrix_nonsingular {p : ZV} (h : zNorm p ≠ 0) :
    (qMatrix p).det ≠ 0 ∧ (qMatrix (zConj p)).det ≠ 0 := by
  have he := congrArg Matrix.det (qMatrix_conjugate p)
  simp only [Matrix.det_mul,Matrix.det_smul,Matrix.det_one,Fintype.card_bool,mul_one] at he
  have hn : (zNorm p : ℂ) ≠ 0 := by exact_mod_cast h
  apply mul_ne_zero_iff.mp
  rw [he]
  exact pow_ne_zero _ hn

theorem liftMatrix_mul (A B : ZEnd) : liftMatrix (A*B)=liftMatrix A*liftMatrix B := by
  ext i j
  simp [liftMatrix,Matrix.mul_apply]

theorem liftMatrix_smul (c : ℤ) (A : ZEnd) : liftMatrix (c • A)=(c : ℂ) • liftMatrix A := by
  ext i j
  simp [liftMatrix]

theorem lift_zLeft (p : ZV) : liftMatrix (zLeft p)=sandwich (qMatrix p) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftMatrix,zLeft,sandwich,qMatrix,assemble,liftVector,coordinates_apply,
      quaternionCoefficient,quaternionBasis,Q0,Q1,Q2,Q3,Holant.Signature.equality,
      Matrix.mul_apply,Matrix.one_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem lift_zRight (p : ZV) : liftMatrix (zRight p)=sandwich 1 (qMatrix p) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftMatrix,zRight,sandwich,qMatrix,assemble,liftVector,coordinates_apply,
      quaternionCoefficient,quaternionBasis,Q0,Q1,Q2,Q3,Holant.Signature.equality,
      Matrix.mul_apply,Matrix.one_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def kindSandwich (b : Bool) (U W : BinaryMatrix) : End :=
  if b then transposeSandwich U W else sandwich U W

theorem lift_zTranspose (b : Bool) : liftMatrix (zTranspose b)=kindSandwich b 1 1 := by
  ext i j
  cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [liftMatrix,zTranspose,kindSandwich,sandwich,transposeSandwich,coordinates_apply,
      quaternionCoefficient,quaternionBasis,Q0,Q1,Q2,Q3,Holant.Signature.equality,
      Matrix.diagonal,Matrix.one_apply,Matrix.transpose_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem sandwich_comp (U W V Z : BinaryMatrix) :
    sandwich U W * sandwich V Z = sandwich (U*V) (Z*W) := by
  apply matrix_ext_action
  intro r
  simp only [← Matrix.mulVec_mulVec,sandwich_action]
  change coordinates (U * assemble (quaternionCoefficient _) * W) = _
  rw [assemble_coefficient]
  simp only [Matrix.mul_assoc]

theorem sandwich_kind_comp (b : Bool) (U W V Z : BinaryMatrix) :
    sandwich U W * kindSandwich b V Z = kindSandwich b (U*V) (Z*W) := by
  cases b
  · exact sandwich_comp U W V Z
  · apply matrix_ext_action
    intro r
    simp only [kindSandwich,ite_true,← Matrix.mulVec_mulVec,sandwich_action,transposeSandwich_action]
    change coordinates (U * assemble (quaternionCoefficient _) * W) = _
    rw [assemble_coefficient]
    simp only [Matrix.mul_assoc]

theorem kindSandwich_smul_right (b : Bool) (U W : BinaryMatrix) (c : ℂ) :
    kindSandwich b U (c • W)=c • kindSandwich b U W := by
  cases b <;> ext i j <;>
    simp [kindSandwich,sandwich,transposeSandwich,Matrix.mul_smul,map_smul]
  all_goals exact RainbowOrbit.quaternionCoefficient_smul c _ i

theorem kindSandwich_smul_left (b : Bool) (U W : BinaryMatrix) (c : ℂ) :
    kindSandwich b (c • U) W=c • kindSandwich b U W := by
  cases b <;> ext i j <;>
    simp [kindSandwich,sandwich,transposeSandwich,Matrix.smul_mul,map_smul]
  all_goals exact RainbowOrbit.quaternionCoefficient_smul c _ i

theorem signedMap_normal_form (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    ∃ U W : BinaryMatrix, U.det ≠ 0 ∧ W.det ≠ 0 ∧
      signedMap σ ε=kindSandwich (normalTranspose σ ε) U W := by
  let p := normalVector σ ε
  let n : ℂ := zNorm p
  have hn : n ≠ 0 := by
    dsimp [n,p]
    exact_mod_cast normal_norm_ne_zero σ ε
  have hp := qMatrix_nonsingular (normal_norm_ne_zero σ ε)
  have he := congrArg liftMatrix (normal_identity σ ε)
  rw [liftMatrix_mul,liftMatrix_mul,liftMatrix_smul,lift_zLeft,lift_zRight,lift_zTranspose,
    sandwich_comp,sandwich_kind_comp] at he
  simp only [Matrix.mul_one,Matrix.one_mul] at he
  change kindSandwich (normalTranspose σ ε) (qMatrix p) (qMatrix (zConj p)) = n • signedMap σ ε at he
  refine ⟨qMatrix p,n⁻¹ • qMatrix (zConj p),hp.1,?_,?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hn)) hp.2
  · rw [kindSandwich_smul_right,he,smul_smul,inv_mul_cancel₀ hn,one_smul]

theorem leftMap_normal_form (k : Fin 12) : leftMap k=sandwich (qMatrix (zstandard k)) 1 :=
  lift_zLeft (zstandard k)

theorem standard_rank_four_normal_forms (A : End) (hA : A.rank=4) (h : TwoSided Standard A) :
    ∃ U W : BinaryMatrix, U.det ≠ 0 ∧ W.det ≠ 0 ∧
      (A=sandwich U W ∨ A=transposeSandwich U W) := by
  obtain ⟨⟨k,σ,ε⟩,c,hc,rfl⟩ := (standard_full_rank_twoSided A hA).mp h
  obtain ⟨U,W,hU,hW,he⟩ := signedMap_normal_form σ ε
  have hq := (qMatrix_nonsingular (zstandard_norm_ne_zero k)).1
  refine ⟨c • (qMatrix (zstandard k)*U),W,?_,hW,?_⟩
  · rw [Matrix.det_smul,Matrix.det_mul]
    exact mul_ne_zero (pow_ne_zero _ hc) (mul_ne_zero hq hU)
  · change c • (leftMap k*signedMap σ ε)=sandwich _ _ ∨
      c • (leftMap k*signedMap σ ε)=transposeSandwich _ _
    rw [leftMap_normal_form,he,sandwich_kind_comp,Matrix.mul_one,← kindSandwich_smul_left]
    cases hb : normalTranspose σ ε <;> simp [kindSandwich,hb]

theorem external_rank_four_normal_forms (A : End) (hA : A.rank=4) (h : TwoSided External A) :
    ∃ U W : BinaryMatrix, U.det ≠ 0 ∧ W.det ≠ 0 ∧
      (A=sandwich U W ∨ A=transposeSandwich U W) := by
  obtain ⟨U,W,hU,hW,he | he⟩ := standard_rank_four_normal_forms (toStandard A)
    (by simpa using hA) ((standard_twoSided_iff A).mpr h)
  · refine ⟨sourceTheta U,sourceTheta W,sourceTheta_det_ne_zero hU,sourceTheta_det_ne_zero hW,
      Or.inl ?_⟩
    simpa only [toExternal_toStandard,toExternal_sandwich] using congrArg toExternal he
  · refine ⟨sourceRInv*U*sourceRInv,sourceR*W*sourceR,?_,?_,Or.inr ?_⟩
    · simp only [Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero sourceR_dets.2 hU) sourceR_dets.2
    · simp only [Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero sourceR_dets.1 hW) sourceR_dets.1
    · simpa only [toExternal_toStandard,toExternal_transposeSandwich] using congrArg toExternal he

/-- Every arbitrary complex external rank-four preserver reconstructs a
product of two nonsingular binaries on one of the crossing matchings. -/
theorem external_rank_four_reconstruction (A : End) (hA : A.rank=4) (h : TwoSided External A) :
    ∃ U W : BinaryMatrix, U.det ≠ 0 ∧ W.det ≠ 0 ∧
      (reconstruct A=P1 U W ∨ reconstruct A=P2 U W) := by
  obtain ⟨U,W,hU,hW,rfl | rfl⟩ := external_rank_four_normal_forms A hA h
  · exact ⟨U.transpose,W,by simpa using hU,hW,Or.inl (reconstruct_sandwich U W)⟩
  · exact ⟨W,U.transpose,hW,by simpa using hU,Or.inr (reconstruct_transposeSandwich U W)⟩

end Holant.Certificates.TetrahedralPreservers
