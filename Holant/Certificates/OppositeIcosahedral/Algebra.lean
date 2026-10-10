import Holant.Certificates.OppositeIcosahedral.Data

namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem D_diagonal (a b : Bool) : D a b=if a=b then (if a then 1-Complex.I else 1+Complex.I) else 0 := by
  cases a <;> cases b <;> simp [D,Q0,Q3,Signature.equality,sub_eq_add_neg]

theorem D_Dinv : D*Dinv=(1 : Mat) := by
  ext a b
  cases a <;> cases b <;> simp [D,Dinv,Q0,Q3,Signature.equality,Matrix.mul_apply,Matrix.smul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem Dinv_D : Dinv*D=(1 : Mat) := by
  ext a b
  cases a <;> cases b <;> simp [D,Dinv,Q0,Q3,Signature.equality,Matrix.mul_apply,Matrix.smul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem D_det : D.det=2 := by
  change (Matrix.of D).det=2
  rw [←binaryDeterminant_eq_det]
  simp [binaryDeterminant,D,Q0,Q3,Signature.equality]
  ring_nf
  simp [Complex.I_sq]
  norm_num

theorem D_det_ne_zero : D.det≠0 := by rw [D_det]; norm_num

theorem D_inverse : D⁻¹=Dinv := Matrix.inv_eq_right_inv D_Dinv

theorem D_transpose : D.transpose=D := by ext a b; cases a <;> cases b <;> rfl

theorem Dinv_transpose : Dinv.transpose=Dinv := by ext a b; cases a <;> cases b <;> rfl

theorem native_edge_scalar : D.transpose*X*D=(2 : ℂ) • X := by
  ext a b
  cases a <;> cases b <;> simp [D,X,Q0,Q3,Signature.equality,Signature.disequality,Matrix.mul_apply,
    Matrix.smul_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem inverse_transpose_source : Dinv.transpose=(1/2 : ℂ) • (X*D*X) := by
  ext a b
  cases a <;> cases b <;> simp [D,Dinv,X,Q0,Q3,Signature.equality,Signature.disequality,Matrix.mul_apply,
    Matrix.smul_apply] <;> ring

theorem conjugate_smul (c : ℂ) (U : Mat) : conjugate (c • U)=c • conjugate U := by
  simp [conjugate,Matrix.mul_smul,Matrix.smul_mul]

theorem pull_smul (c : ℂ) (U : Mat) : pull (c • U)=c • pull U := by
  simp [pull,Matrix.mul_smul,Matrix.smul_mul]

theorem kappa_smul (c : ℂ) (U : Mat) : kappa (c • U)=c • kappa U := by
  simp [kappa,Matrix.mul_smul,Matrix.smul_mul]

theorem conjugate_pull (U : Mat) : conjugate (pull U)=U := by
  simp only [conjugate,pull,mul_assoc,D_Dinv,mul_one]
  rw [←mul_assoc D,D_Dinv,one_mul]

theorem pull_conjugate (U : Mat) : pull (conjugate U)=U := by
  simp only [conjugate,pull,mul_assoc,Dinv_D,mul_one]
  rw [←mul_assoc Dinv,Dinv_D,one_mul]

theorem kappa_unkappa (U : Mat) : kappa (unkappa U)=U := by
  simp only [kappa,unkappa,D_transpose,Dinv_transpose,mul_assoc,D_Dinv,mul_one]
  rw [←mul_assoc Dinv,Dinv_D,one_mul]

theorem unkappa_kappa (U : Mat) : unkappa (kappa U)=U := by
  simp only [kappa,unkappa,D_transpose,Dinv_transpose,mul_assoc,Dinv_D,mul_one]
  rw [←mul_assoc D,D_Dinv,one_mul]

/-- Exact scalar dictionary: the finite index is the checked left-Q3 product. -/
theorem kappa_Q3_dictionary (U : Mat) :
    kappa U=(-1/2 : ℂ) • conjugate ((Matrix.of Q3)*U) := by
  ext a b
  cases a <;> cases b <;>
    simp [kappa,conjugate,D,Dinv,Q0,Q3,Signature.equality,Matrix.mul_apply,Matrix.smul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem conjugate_quaternion (v : Fin 4→ℝ) :
    conjugate (Matrix.of (quaternion v))=Matrix.of (quaternion (twistVector chiralitySwap forwardSigns v)) := by
  ext a b
  cases a <;> cases b <;>
    simp [conjugate,D,Dinv,quaternion,twistVector,chiralitySwap,forwardSigns,signBit,
      Q0,Q1,Q2,Q3,Signature.equality,Matrix.mul_apply,Matrix.smul_apply,Equiv.swap_apply_def] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem pull_quaternion (v : Fin 4→ℝ) :
    pull (Matrix.of (quaternion v))=Matrix.of (quaternion (twistVector chiralitySwap inverseSigns v)) := by
  ext a b
  cases a <;> cases b <;>
    simp [pull,D,Dinv,quaternion,twistVector,chiralitySwap,inverseSigns,signBit,
      Q0,Q1,Q2,Q3,Signature.equality,Matrix.mul_apply,Matrix.smul_apply,Equiv.swap_apply_def] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

end
end Holant.Certificates.OppositeIcosahedral
