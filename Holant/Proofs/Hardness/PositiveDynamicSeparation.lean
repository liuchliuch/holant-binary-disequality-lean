import Holant.Proofs.Hardness.PositiveDynamicParameters
import Holant.Proofs.Hardness.PositiveDynamicStage

/-! Unnormalized finite-grid separation in the original coefficient field.
All chain coefficients are explicit field arithmetic expressions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicSeparation

section Field
variable {K : Type*} [Field K]
/-- First pair coefficient of the n-copy original signature chain. -/
def chainA (a b : K) (n : ℕ) : K := ((a+b)^n-(b-a)^n)/2
/-- Second pair coefficient of the n-copy original signature chain. -/
def chainB (a b : K) (n : ℕ) : K := ((a+b)^n+(b-a)^n)/2
/-- Distinguished first mode after the physical port transposition. -/
def lam (a b : K) (n : ℕ) : K := chainA a b n
/-- The two other eigenmodes after the physical port transposition. -/
def mu (a b c : K) (n : ℕ) : K := chainB a b n+c^n
def nu (a b c : K) (n : ℕ) : K := chainB a b n-c^n
end Field

namespace Real
variable (d : PositiveDynamicParameters.Data)

theorem lam_normalized (m : ℕ) :
    lam d.a d.b (d.length m)=d.mu^(d.length m)*PositiveDynamicNormalized.A (d.delta m) := by
  have hm : d.mu≠0 := ne_of_gt d.mu_pos
  change (d.mu^(d.length m)-d.nu^(d.length m))/2=
    d.mu^(d.length m)*((1-(d.nu/d.mu)^(d.length m))/2)
  rw [div_pow]
  field_simp [pow_ne_zero (d.length m) hm]

theorem mu_normalized (m : ℕ) :
    mu d.a d.b d.c (d.length m)=
      d.mu^(d.length m)*(PositiveDynamicNormalized.B (d.delta m)+d.epsilon m) := by
  have hm : d.mu≠0 := ne_of_gt d.mu_pos
  change (d.mu^(d.length m)+d.nu^(d.length m))/2+d.c^(d.length m)=
    d.mu^(d.length m)*((1+(d.nu/d.mu)^(d.length m))/2+(d.c/d.mu)^(d.length m))
  rw [div_pow,div_pow]
  field_simp [pow_ne_zero (d.length m) hm]

theorem nu_normalized (m : ℕ) :
    nu d.a d.b d.c (d.length m)=
      d.mu^(d.length m)*(PositiveDynamicNormalized.B (d.delta m)-d.epsilon m) := by
  have hm : d.mu≠0 := ne_of_gt d.mu_pos
  change (d.mu^(d.length m)+d.nu^(d.length m))/2-d.c^(d.length m)=
    d.mu^(d.length m)*((1+(d.nu/d.mu)^(d.length m))/2-(d.c/d.mu)^(d.length m))
  rw [div_pow,div_pow]
  field_simp [pow_ne_zero (d.length m) hm]

theorem lam_pos (m : ℕ) : 0<lam d.a d.b (d.length m) := by
  rw [lam_normalized]
  apply mul_pos (pow_pos d.mu_pos _)
  obtain ⟨he,hs⟩ := d.epsilon_bounds m
  obtain ⟨hd,hde⟩ := d.delta_bounds m
  have hm : 0≤(m:ℝ) := Nat.cast_nonneg _
  have h := (lt_div_iff₀ (by positivity : (0:ℝ)<128*((m:ℝ)+1))).mp hs
  have he1 : d.epsilon m<1/128 := by nlinarith [mul_nonneg he.le hm]
  dsimp [PositiveDynamicNormalized.A]
  nlinarith

/-- This is a finite-size statement: the chain length depends on m. -/
theorem coefficients_ne (m : ℕ) {i j : ℕ} (hij : i+j≤m) (hpos : 0 < i + j) :
    (lam d.a d.b (d.length m))^(i+j)≠
      (mu d.a d.b d.c (d.length m))^i*(nu d.a d.b d.c (d.length m))^j := by
  rw [lam_normalized,mu_normalized,nu_normalized]
  intro he
  apply d.coefficients_ne m hij hpos
  apply mul_left_cancel₀ (pow_ne_zero (i+j) (pow_ne_zero (d.length m) (ne_of_gt d.mu_pos)))
  simpa only [mul_pow,pow_add,mul_assoc,mul_left_comm,mul_comm] using he

/-- Desired finite annihilator root avoids every unwanted root, with repetitions allowed. -/
theorem desired_ne_mode (m : ℕ) {ij : ℕ×ℕ} (hij : ij∈ThreeModeAnnihilator.unwanted m) :
    (lam d.a d.b (d.length m))^m≠
      ThreeModeAnnihilator.mode m (lam d.a d.b (d.length m)) (mu d.a d.b d.c (d.length m))
        (nu d.a d.b d.c (d.length m)) ij := by
  rcases ij with ⟨i,j⟩
  obtain ⟨hs,hpos⟩ := ThreeModeAnnihilator.mem_unwanted.mp hij
  intro he
  apply coefficients_ne d m hs hpos
  apply mul_left_cancel₀ (pow_ne_zero (m-i-j) (ne_of_gt (lam_pos d m)))
  have hexp : (m-i-j)+(i+j)=m := by omega
  rw [←pow_add,hexp]
  simpa only [ThreeModeAnnihilator.mode,mul_assoc] using he

/-- The original finite filter denominator is nonzero, including m=0. -/
theorem denominator_nonzero (m : ℕ) :
    ThreeModeAnnihilator.denominator m (lam d.a d.b (d.length m)) (mu d.a d.b d.c (d.length m))
      (nu d.a d.b d.c (d.length m))≠0 := by
  apply mul_ne_zero (pow_ne_zero m (ne_of_gt (lam_pos d m)))
  rw [ThreeModeAnnihilator.polynomial_eval]
  exact Finset.prod_ne_zero_iff.mpr (fun ij hij=>sub_ne_zero.mpr (desired_ne_mode d m hij))

end Real

section EmbeddedField
variable {K : Type*} [Field K] (σ : K →+* ℝ) (a b c : K) (d : PositiveDynamicParameters.Data)
variable (ha : σ a=d.a) (hb : σ b=d.b) (hc : σ c=d.c)

include ha hb hc in
/-- Original generated-field statement; the real embedding is used only in the proof. -/
theorem desired_ne_mode (m : ℕ) {ij : ℕ×ℕ} (hij : ij∈ThreeModeAnnihilator.unwanted m) :
    (lam a b (d.length m))^m≠
      ThreeModeAnnihilator.mode m (lam a b (d.length m)) (mu a b c (d.length m))
        (nu a b c (d.length m)) ij := by
  intro he
  apply Real.desired_ne_mode d m hij
  have he' := congrArg σ he
  simpa only [ThreeModeAnnihilator.mode,lam,mu,nu,chainA,chainB,map_mul,map_div₀,map_sub,map_pow,map_add,map_ofNat,ha,hb,hc] using he'

include ha hb in
theorem lam_nonzero (m : ℕ) : lam a b (d.length m)≠0 := by
  intro he
  have he' := congrArg σ he
  have hh : lam d.a d.b (d.length m)=0 := by
    simpa only [lam,chainA,map_zero,map_div₀,map_sub,map_pow,map_add,map_ofNat,ha,hb] using he'
  exact (ne_of_gt (Real.lam_pos d m)) hh

include ha hb hc in
/-- Exact nonzero denominator API for the original-field dynamic filter. -/
theorem denominator_nonzero (m : ℕ) :
    ThreeModeAnnihilator.denominator m (lam a b (d.length m)) (mu a b c (d.length m))
      (nu a b c (d.length m))≠0 := by
  apply mul_ne_zero (pow_ne_zero m (lam_nonzero σ a b d ha hb m))
  rw [ThreeModeAnnihilator.polynomial_eval]
  exact Finset.prod_ne_zero_iff.mpr
    (fun ij hij=>sub_ne_zero.mpr (desired_ne_mode σ a b c d ha hb hc m hij))

/-- The explicit field expressions are exactly the three modes of the physical stage. -/
theorem stage_denote [CharZero K] (n : ℕ) (hn : 0<n) :
    (PositiveDynamicStage.stage a b c n).denote=ThreeModeSignatures.spectral
      (lam a b n) (mu a b c n) (nu a b c n) :=
  PositiveDynamicStage.stage_denote a b c n hn

end EmbeddedField
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicSeparation
