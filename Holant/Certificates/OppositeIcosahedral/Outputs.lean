import Holant.Certificates.OppositeIcosahedral.DiagonalTransport
import Holant.Certificates.RainbowOrbit.Action

namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def binaryTransport (B : Mat) : Mat := D*B*D.transpose

theorem binary_transfer_exact (B : Mat) : binaryTransport B*X=(2 : ℂ) • conjugate (B*X) := by
  ext a b
  cases a <;> cases b <;>
    simp [binaryTransport,conjugate,D,Dinv,X,Q0,Q3,Signature.equality,Signature.disequality,
      Matrix.mul_apply,Matrix.smul_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem Direction.smul_iff (U : Mat) (c : ℂ) (hc : c≠0) : Direction (c • U) ↔ Direction U := by
  constructor
  · intro h
    have hh := h.smul (inv_ne_zero hc)
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hh
  · exact fun h => h.smul hc

/-- Safe and outside transfers are both preserved against the complete actual
opposite group, with the exact edge scalar2 shown above. -/
theorem output_transfer_iff (B : Mat) :
    Direction (binaryTransport B*X) ↔ groupDirection .icosahedral (B*X) := by
  rw [binary_transfer_exact,Direction.smul_iff _ 2 (by norm_num),direction_conjugate_iff]

theorem outside_transfer_iff (B : Mat) :
    ¬Direction (binaryTransport B*X) ↔ ¬groupDirection .icosahedral (B*X) :=
  not_congr (output_transfer_iff B)

theorem binary_nonsingular_iff (B : Mat) : (binaryTransport B).det≠0 ↔ B.det≠0 := by
  simp only [binaryTransport,Matrix.det_mul,Matrix.det_transpose,D_det]
  simp

theorem binary_support_iff (B : Mat) (a b : Bool) : binaryTransport B a b≠0 ↔ B a b≠0 := by
  have he : binaryTransport B a b=(diagonalWeight a*diagonalWeight b)*B a b := by
    cases a <;> cases b <;>
      simp [binaryTransport,D_weight,Matrix.mul_apply,Signature.equality] <;> ring
  rw [he]
  simp [diagonalWeight_ne_zero]

theorem matching_label_preserved (r : Fin 3) (U V : Mat) :
    transport (matchingTensor r U V)=matchingTensor r (binaryTransport U) (binaryTransport V) := by
  fin_cases r
  · exact RainbowOrbit.act_P0 (fun _ => D) U V
  · exact RainbowOrbit.act_P1 (fun _ => D) U V
  · exact RainbowOrbit.act_P2 (fun _ => D) U V

theorem card_flattening_ranks {n : ℕ} {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I⊕J≃Fin n) (p : Equiv.Perm (Fin (n+2))) (f : Signature ℂ (n+2)) (K : Mat) :
    (Marked.WeightedGauge.flatten e (card p f (kappa K))).rank=
      (Marked.WeightedGauge.flatten e (card p (analytical f) K)).rank := by
  rw [card_covariance,transport_eq_tensor]
  exact all_flattening_ranks e _

theorem card_factorization {n : ℕ} (p : Equiv.Perm (Fin (n+2))) (f : Signature ℂ (n+2)) (K : Mat)
    (F : TensorDecomposition ℂ n) :
    (transportedDecomposition F).value=card p f (kappa K) ↔ F.value=card p (analytical f) K := by
  rw [card_covariance]
  exact factorization_iff F _

end
end Holant.Certificates.OppositeIcosahedral
