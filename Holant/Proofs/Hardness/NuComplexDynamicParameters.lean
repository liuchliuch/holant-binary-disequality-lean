import Holant.Proofs.Hardness.ComplexDynamicParameters

/-! Damping parameters for the b-a dominant cone. Only the natural damping
constant is obtained from auxiliary coefficients (-a,b,c); all physical
queries and their signatures retain the original coefficients (a,b,c). -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.NuComplexDynamicParameters

structure Data where
  a : ℂ
  b : ℂ
  c : ℂ
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  c_ne : c ≠ 0
  nu_ne : b-a ≠ 0
  ratio_lt : ‖c/(b-a)‖ < 1
  oddRatio_lt : ‖(a+b)*(b-a)‖/‖c‖^2 < 1

namespace Data
variable (d : Data)
def mu : ℂ := d.a+d.b
def nu : ℂ := d.b-d.a

def dampingData : ComplexDynamicParameters.Data where
  a := -d.a
  b := d.b
  c := d.c
  a_ne := neg_ne_zero.mpr d.a_ne
  b_ne := d.b_ne
  c_ne := d.c_ne
  mu_ne := by simpa only [sub_eq_add_neg, add_comm] using d.nu_ne
  ratio_lt := by simpa only [sub_eq_add_neg, add_comm] using d.ratio_lt
  oddRatio_lt := by simpa only [sub_neg_eq_add, sub_eq_add_neg, neg_neg, add_comm] using d.oddRatio_lt

theorem dampingData_mu : d.dampingData.mu = d.nu := by
  dsimp [dampingData, ComplexDynamicParameters.Data.mu, nu]
  ring

theorem dampingData_nu : d.dampingData.nu = d.mu := by
  dsimp [dampingData, ComplexDynamicParameters.Data.nu, mu]
  ring

theorem dampingData_c : d.dampingData.c = d.c := rfl

def realParams : PositiveDynamicParameters.Data := d.dampingData.realParams
def constant : ℕ := d.dampingData.constant
def length (m : ℕ) : ℕ := d.constant*(m+1)
def epsilon (m : ℕ) : ℂ := (d.c/d.nu)^(d.length m)
def delta (m : ℕ) : ℂ := (d.mu/d.nu)^(d.length m)

theorem nu_nonzero : d.nu ≠ 0 := d.nu_ne

theorem length_eq (m : ℕ) : d.length m = d.dampingData.length m := rfl

theorem length_linear (m : ℕ) : d.length m = d.constant*(m+1) := rfl

theorem constant_spec : 0<d.constant ∧ Even d.constant ∧
    d.dampingData.rho^d.constant<1/256 := d.dampingData.constant_spec

theorem length_pos (m : ℕ) : 0<d.length m := d.dampingData.length_pos m

theorem epsilon_bounds (m : ℕ) : 0<‖d.epsilon m‖ ∧
    ‖d.epsilon m‖<1/(128*((m:ℝ)+1)^2) := by
  simpa only [ComplexDynamicParameters.Data.epsilon, dampingData_mu, ←length_eq,
    epsilon, dampingData_c] using d.dampingData.epsilon_bounds m

theorem delta_bounds (m : ℕ) : ‖d.delta m‖≤‖d.epsilon m‖^2/4 := by
  simpa only [ComplexDynamicParameters.Data.delta, ComplexDynamicParameters.Data.epsilon,
    dampingData_mu, dampingData_nu, ←length_eq, delta, epsilon, dampingData_c] using d.dampingData.delta_bounds m

end Data
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.NuComplexDynamicParameters
