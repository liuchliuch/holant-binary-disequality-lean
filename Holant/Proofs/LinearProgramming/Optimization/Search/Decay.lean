import Holant.Proofs.LinearProgramming.Optimization.Search.Scales

/-!
An explicit polynomial block size halves the proved determinant upper bound.
Bernoulli is applied to the reciprocal contraction, so no real logarithm,
asymptotic estimate, or supplied iteration bound enters the proof.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Decay

def block (n : ℕ) : ℕ := 2*(n^3+1)

theorem block_pos (n : ℕ) : 0<block n := by unfold block; omega

theorem block_identity (n : ℕ) :
    (block n:ℚ)*(1-Scales.contraction n)=1 := by
  unfold block Scales.contraction
  push_cast
  have h : (n:ℚ)^3+1≠0 := ne_of_gt (by positivity : (0:ℚ)<(n:ℚ)^3+1)
  field_simp [h]
  <;> ring

theorem block_halves (n : ℕ) : Scales.contraction n^block n≤1/2 := by
  let r := Scales.contraction n
  have hr : 0<r := Scales.contraction_pos n
  have hr1 : r<1 := Scales.contraction_lt_one n
  have hne : r≠0 := ne_of_gt hr
  have hkr : (block n:ℚ)*(1-r)=1 := block_identity n
  have hinv : 1≤r⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hr1.le)
  have he : (block n:ℚ)*(r⁻¹-1)=r⁻¹ := by
    have he' : r⁻¹-1=(1-r)/r := by field_simp [hne] <;> ring
    rw [he',← mul_div_assoc,hkr,one_div]
  have hb := one_add_mul_le_pow (show (-2:ℚ)≤r⁻¹-1 by linarith) (block n)
  rw [add_sub_cancel,he] at hb
  have hp := pow_nonneg hr.le (block n)
  have hm := mul_le_mul_of_nonneg_right hb hp
  rw [← mul_pow,inv_mul_cancel₀ hne,one_pow] at hm
  have htwo : 2≤1+r⁻¹ := by linarith
  have ht := (mul_le_mul_of_nonneg_right htwo hp).trans hm
  change r^block n≤(1:ℚ)/2
  exact (le_div_iff₀ (by norm_num : (0:ℚ)<2)).mpr (by nlinarith [ht])

theorem blocks_decay (n k : ℕ) :
    Scales.contraction n^(block n*k)≤1/((2^k:ℕ):ℚ) := by
  rw [pow_mul]
  have h := pow_le_pow_left₀ (pow_nonneg (Scales.contraction_pos n).le _)
    (block_halves n) k
  simpa only [div_pow,one_pow,Nat.cast_pow,Nat.cast_ofNat] using h

end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Decay
