import Holant.Certificates.RainbowOrbit.ExternalData
import Holant.Certificates.RainbowOrbit.GroupRepresentatives

/-! The actual twelve external tetrahedral directions. Group operations and
projective separation are proved for arbitrary complex scalars. -/
namespace Holant.Certificates.RainbowOrbit.External
noncomputable section
open Holant.Certificates.OctahedralSeparator
open Holant.Certificates.MatchingProductBridge
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def representative (k : Fin 12) : Matrix Bool Bool ℂ := complexMatrix (raw k)

/-- Nonzero complex projective saturation of the fixed actual dictionary. -/
def Direction (U : Matrix Bool Bool ℂ) : Prop :=
  ∃ k : Fin 12, ∃ c : ℂ, c ≠ 0 ∧ U = c • representative k

theorem tetrahedral_restriction : ∀ k : Fin 12,
    octahedralRaw (firstTwelve k) = tetrahedralRaw k := by decide +kernel

theorem representative_eq_theta (k : Fin 12) :
    representative k = complexTheta 2 (RainbowOrbit.representative .tetrahedral k) := by
  unfold representative raw
  rw [complexMatrix_theta,← octahedralRaw_standard,tetrahedral_restriction]
  rfl

theorem representative_det_ne_zero (k : Fin 12) : Matrix.det (representative k) ≠ 0 := by
  rw [representative_eq_theta]
  have hH := complexMatrix_conjugator_det_ne_zero 2
  have hV := RainbowOrbit.representative_det_ne_zero .tetrahedral k
  simp only [complexTheta,Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
  exact mul_ne_zero (inv_ne_zero hH) (mul_ne_zero hV hH)

theorem representative_ne_zero (k : Fin 12) : representative k ≠ 0 := by
  intro h
  have hd := representative_det_ne_zero k
  rw [h,Matrix.det_zero] at hd
  exact hd rfl

theorem projectively_injective (i j : Fin 12) (c : ℂ)
    (h : representative i = c • representative j) : i=j := by
  have hp := congrArg (complexPull 2) h
  simp only [representative_eq_theta,complexPull_smul,complexPull_complexTheta] at hp
  exact RainbowOrbit.projectively_injective .tetrahedral i j c hp

theorem complexTheta_mul (f : Form) (U V : Matrix Bool Bool ℂ) :
    complexTheta f (U*V) = complexTheta f U*complexTheta f V := by
  have hH := Matrix.mul_nonsing_inv (complexMatrix (conjugator f))
    (isUnit_iff_ne_zero.mpr (complexMatrix_conjugator_det_ne_zero f))
  simp only [complexTheta,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (complexMatrix (conjugator f))
    (complexMatrix (conjugator f))⁻¹,hH,Matrix.one_mul]

theorem mul_exact (i j : Fin 12) :
    representative i*representative j =
      (tetrahedralProductScale i j : ℂ) • representative (tetrahedralProductIndex i j) := by
  simp only [representative_eq_theta]
  rw [← complexTheta_mul,RainbowOrbit.mul_exact,complexTheta_smul]
  rfl

theorem mul_certificate (i j : Fin 12) : ∃ k : Fin 12, ∃ c : ℂ,
    c ≠ 0 ∧ representative i*representative j = c • representative k :=
  ⟨tetrahedralProductIndex i j,tetrahedralProductScale i j,
    Int.cast_ne_zero.mpr (RainbowOrbit.raw_certificate .tetrahedral i j).1,mul_exact i j⟩

theorem transpose_exact (k : Fin 12) : (representative k).transpose =
    embed (transposeScale k) • representative (transposeIndex k) := by
  rw [representative,← complexMatrix_mt,raw_transpose,complexMatrix_ms]
  rfl

theorem inverse_exact (k : Fin 12) : (representative k)⁻¹ =
    embed (inverseScale k) • representative (inverseIndex k) := by
  apply Matrix.inv_eq_right_inv
  change complexMatrix (raw k) * (embed (inverseScale k) • complexMatrix (raw (inverseIndex k))) = 1
  rw [← complexMatrix_ms,← complexMatrix_mm,raw_right_inverse,complexMatrix_q0]

namespace Direction

theorem representative (k : Fin 12) : Direction (External.representative k) :=
  ⟨k,1,one_ne_zero,by simp⟩

theorem smul {U : Matrix Bool Bool ℂ} (hU : Direction U) {c : ℂ} (hc : c ≠ 0) :
    Direction (c • U) := by
  obtain ⟨k,d,hd,rfl⟩ := hU
  exact ⟨k,c*d,mul_ne_zero hc hd,by rw [smul_smul]⟩

theorem mul {U V : Matrix Bool Bool ℂ} (hU : Direction U) (hV : Direction V) :
    Direction (U*V) := by
  obtain ⟨i,c,hc,rfl⟩ := hU
  obtain ⟨j,d,hd,rfl⟩ := hV
  obtain ⟨k,e,he,hk⟩ := mul_certificate i j
  refine ⟨k,c*d*e,mul_ne_zero (mul_ne_zero hc hd) he,?_⟩
  rw [Matrix.smul_mul,Matrix.mul_smul,hk]
  simp [smul_smul,mul_assoc]

theorem det_ne_zero {U : Matrix Bool Bool ℂ} (hU : Direction U) : Matrix.det U ≠ 0 := by
  obtain ⟨i,c,hc,rfl⟩ := hU
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) (representative_det_ne_zero i)

theorem transpose {U : Matrix Bool Bool ℂ} (hU : Direction U) : Direction U.transpose := by
  obtain ⟨i,c,hc,rfl⟩ := hU
  rw [Matrix.transpose_smul,transpose_exact]
  exact ((representative _).smul (embed_ne_zero (transposeScale_ne_zero i))).smul hc

theorem inverse {U : Matrix Bool Bool ℂ} (hU : Direction U) : Direction U⁻¹ := by
  obtain ⟨i,c,hc,rfl⟩ := hU
  have hi : (c • External.representative i)⁻¹ = c⁻¹ • (External.representative i)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (representative_det_ne_zero i))]
    simp [hc]
  rw [hi,inverse_exact]
  exact ((representative _).smul (embed_ne_zero (inverseScale_ne_zero i))).smul (inv_ne_zero hc)

theorem inverseTranspose {U : Matrix Bool Bool ℂ} (hU : Direction U) : Direction U⁻¹.transpose :=
  hU.inverse.transpose

end Direction

theorem representative_identity : representative 0 = 1 := by
  have h : raw 0 = q 0 := by decide +kernel
  rw [representative,h,complexMatrix_q0]

theorem representative_Q1 : representative 1 = Matrix.of Q1 := by
  have h : raw 1 = q 1 := by decide +kernel
  rw [representative,h,complexMatrix_q]
  rfl

theorem direction_one : Direction (1 : Matrix Bool Bool ℂ) := by
  rw [← representative_identity]
  exact Direction.representative 0

theorem direction_X : Direction (Matrix.of X) := by
  have h : Matrix.of X = (-Complex.I) • representative 1 := by
    rw [representative_Q1]
    ext a b
    cases a <;> cases b <;> simp [X,Q1,Holant.Signature.disequality]
  rw [h]
  exact (Direction.representative 1).smul (neg_ne_zero.mpr Complex.I_ne_zero)

/-- Arbitrary complex proportionality cannot add either omitted Pauli axis. -/
theorem omitted_axis (axis : Fin 2) :
    ¬Direction (complexMatrix (q (if axis=0 then 2 else 3))) := by
  rintro ⟨k,z,hz,h⟩
  obtain ⟨a,b,c,d,hn⟩ := omitted_cross k axis
  apply embed_ne_zero hn
  have hab := congrFun (congrFun h a) b
  have hcd := congrFun (congrFun h c) d
  change embed (q (if axis=0 then 2 else 3) a b) = z*embed (raw k a b) at hab
  change embed (q (if axis=0 then 2 else 3) c d) = z*embed (raw k c d) at hcd
  rw [embed_sub,embed_mul,embed_mul,hab,hcd]
  ring

theorem not_direction_Q2 : ¬Direction (Matrix.of Q2) := by
  simpa [complexMatrix_q,quaternionBasis] using omitted_axis 0

theorem not_direction_Q3 : ¬Direction (Matrix.of Q3) := by
  simpa [complexMatrix_q,quaternionBasis] using omitted_axis 1

end
end Holant.Certificates.RainbowOrbit.External
