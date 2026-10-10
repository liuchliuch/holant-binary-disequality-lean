import Holant.Proofs.Hardness.PositiveDynamicParameters
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Complex norm-cone inputs. A real auxiliary signature chooses only a fixed
integer damping multiplier; no real embedding of the coefficient field is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicParameters

structure Data where
  a : ℂ
  b : ℂ
  c : ℂ
  a_ne : a≠0
  b_ne : b≠0
  c_ne : c≠0
  mu_ne : a+b≠0
  ratio_lt : ‖c/(a+b)‖<1
  oddRatio_lt : ‖(b-a)*(a+b)‖/‖c‖^2<1

namespace Data
variable (d : Data)
def mu : ℂ := d.a+d.b
def nu : ℂ := d.b-d.a
def ratio : ℝ := ‖d.c/d.mu‖
def oddRatio : ℝ := ‖d.nu*d.mu‖/‖d.c‖^2
def rho : ℝ := max (1/2) (max (Real.sqrt d.ratio) (Real.sqrt d.oddRatio))
theorem mu_nonzero : d.mu≠0 := d.mu_ne
theorem ratio_pos : 0<d.ratio := norm_pos_iff.mpr (div_ne_zero d.c_ne d.mu_nonzero)
theorem ratio_lt_one : d.ratio<1 := d.ratio_lt
theorem oddRatio_nonneg : 0≤d.oddRatio := div_nonneg (norm_nonneg _) (sq_nonneg _)
theorem oddRatio_lt_one : d.oddRatio<1 := d.oddRatio_lt
theorem half_le_rho : 1/2≤d.rho := le_max_left _ _
theorem rho_pos : 0<d.rho := lt_of_lt_of_le (by norm_num) d.half_le_rho
theorem rho_lt_one : d.rho<1 := by
  apply max_lt (by norm_num)
  apply max_lt
  · exact (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr (by simpa using d.ratio_lt_one)
  · exact (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr (by simpa using d.oddRatio_lt_one)
theorem ratio_le_rho_sq : d.ratio≤d.rho^2 := by
  have h : Real.sqrt d.ratio≤d.rho := (le_max_left _ _).trans (le_max_right _ _)
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  simpa only [Real.sq_sqrt d.ratio_pos.le] using hp
theorem oddRatio_le_rho_sq : d.oddRatio≤d.rho^2 := by
  have h : Real.sqrt d.oddRatio≤d.rho := (le_max_right _ _).trans (le_max_right _ _)
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  simpa only [Real.sq_sqrt d.oddRatio_nonneg] using hp

/-- Auxiliary damping data. Their coefficients are never substituted for a,b,c. -/
def realParams : PositiveDynamicParameters.Data where
  a := 1
  b := 1
  c := 2*d.rho
  a_pos := by norm_num
  b_pos := by norm_num
  c_pos := mul_pos (by norm_num) d.rho_pos
  a_le_c := by linarith [d.half_le_rho]
  b_le_c := by linarith [d.half_le_rho]
  c_lt_sum := by linarith [d.rho_lt_one]

theorem realParams_ratio : d.realParams.ratio=d.rho := by
  dsimp [realParams,PositiveDynamicParameters.Data.ratio,PositiveDynamicParameters.Data.mu]
  ring

def constant : ℕ := d.realParams.constant
theorem constant_spec : 0<d.constant ∧ Even d.constant ∧ d.rho^d.constant<1/256 := by
  simpa only [constant,realParams_ratio] using d.realParams.constant_spec

def length (m : ℕ) : ℕ := d.realParams.length m
def epsilon (m : ℕ) : ℂ := (d.c/d.mu)^(d.length m)
def delta (m : ℕ) : ℂ := (d.nu/d.mu)^(d.length m)
theorem length_linear (m : ℕ) : d.length m=d.constant*(m+1) := rfl
theorem length_pos (m : ℕ) : 0<d.length m := d.realParams.length_pos m

theorem rho_pow_bounds (m : ℕ) : 0<d.rho^(d.length m) ∧
    d.rho^(d.length m)<1/(128*((m:ℝ)+1)) := by
  simpa only [PositiveDynamicParameters.Data.epsilon,realParams_ratio,length] using
    d.realParams.epsilon_bounds m

theorem epsilon_norm (m : ℕ) : ‖d.epsilon m‖=d.ratio^(d.length m) := norm_pow _ _
theorem epsilon_pos (m : ℕ) : 0<‖d.epsilon m‖ := by
  rw [epsilon_norm]
  exact pow_pos d.ratio_pos _

theorem epsilon_bounds (m : ℕ) : 0<‖d.epsilon m‖ ∧
    ‖d.epsilon m‖<1/(128*((m:ℝ)+1)^2) := by
  refine ⟨d.epsilon_pos m,?_⟩
  have hle : ‖d.epsilon m‖≤(d.rho^(d.length m))^2 := by
    rw [epsilon_norm]
    simpa only [←pow_mul,Nat.mul_comm] using
      pow_le_pow_left₀ d.ratio_pos.le d.ratio_le_rho_sq (d.length m)
  have hs := pow_lt_pow_left₀ (d.rho_pow_bounds m).2 (d.rho_pow_bounds m).1.le (by omega : (2:ℕ)≠0)
  have hm : (0:ℝ)<(m:ℝ)+1 := by positivity
  have hb : (1/(128*((m:ℝ)+1)))^2<1/(128*((m:ℝ)+1)^2) := by
    field_simp
    nlinarith [sq_pos_of_pos hm]
  exact lt_of_le_of_lt hle (hs.trans hb)

theorem oddRatio_identity : ‖d.nu/d.mu‖=d.oddRatio*d.ratio^2 := by
  have hm : ‖d.mu‖≠0 := norm_ne_zero_iff.mpr d.mu_nonzero
  have hc : ‖d.c‖≠0 := norm_ne_zero_iff.mpr d.c_ne
  dsimp [oddRatio,ratio]
  rw [norm_div,norm_mul,norm_div]
  field_simp

theorem delta_norm (m : ℕ) : ‖d.delta m‖=d.oddRatio^(d.length m)*‖d.epsilon m‖^2 := by
  rw [delta,norm_pow,d.oddRatio_identity,mul_pow,epsilon_norm]
  simp only [←pow_mul,Nat.mul_comm]

theorem delta_bounds (m : ℕ) : ‖d.delta m‖≤‖d.epsilon m‖^2/4 := by
  have hu : d.oddRatio^(d.length m)≤(d.rho^(d.length m))^2 := by
    simpa only [←pow_mul,Nat.mul_comm] using
      pow_le_pow_left₀ d.oddRatio_nonneg d.oddRatio_le_rho_sq (d.length m)
  have hp := (d.rho_pow_bounds m).1
  have hs := (d.rho_pow_bounds m).2
  have hm : 0≤(m:ℝ) := Nat.cast_nonneg _
  have hsmall : d.rho^(d.length m)<1/128 := by
    have hh := (lt_div_iff₀ (by positivity : (0:ℝ)<128*((m:ℝ)+1))).mp hs
    nlinarith [mul_nonneg hp.le hm]
  have hu' : d.oddRatio^(d.length m)≤1/4 := by nlinarith
  rw [delta_norm]
  nlinarith [mul_le_mul_of_nonneg_right hu' (sq_nonneg ‖d.epsilon m‖)]

end Data
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicParameters
