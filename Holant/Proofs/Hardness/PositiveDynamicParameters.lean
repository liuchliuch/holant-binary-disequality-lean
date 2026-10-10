import Holant.Proofs.Hardness.PositiveDynamicNormalized
import Mathlib.Algebra.Order.Archimedean.Basic

/-! The chain length is linear in the input count.  Its multiplier is fixed
signature data, chosen once by an Archimedean existence theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicParameters

/-- Fixed positive even damping exponent, independent of the graph size. -/
theorem exists_even_damping {r : ℝ} (hr0 : 0<r) (hr1 : r<1) :
    ∃ C : ℕ, 0<C ∧ Even C ∧ r^C<1/256 := by
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ)<1/256) hr1
  refine ⟨2*(k+1),by omega,even_two_mul _,?_⟩
  exact lt_of_le_of_lt (pow_le_pow_of_le_one hr0.le hr1.le (by omega : k≤2*(k+1))) hk

/-- Elementary geometric decay with a deliberately weak reciprocal bound. -/
theorem mul_pow_le {q : ℝ} (hq0 : 0≤q) (hq : q≤1/2) (m : ℕ) :
    ((m:ℝ)+1)*q^(m+1)≤q := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm : 0≤(m:ℝ) := Nat.cast_nonneg _
    have hp : 0≤q^(m+1) := pow_nonneg hq0 _
    have hmult : ((m:ℝ)+2)*q≤(m:ℝ)+1 := by nlinarith
    have hstep := mul_le_mul_of_nonneg_right hmult hp
    push_cast
    rw [show m+1+1=(m+1)+1 by omega,pow_succ]
    nlinarith

/-- A fixed damping exponent yields the needed size-dependent epsilon. -/
theorem epsilon_small {r : ℝ} {C : ℕ} (hr0 : 0<r)
    (hC : r^C<1/256) (m : ℕ) :
    0<r^(C*(m+1)) ∧ r^(C*(m+1))<1/(128*((m:ℝ)+1)) := by
  refine ⟨pow_pos hr0 _,?_⟩
  have hp : 0≤r^C := (pow_pos hr0 C).le
  have hq : r^C≤1/2 := by linarith
  have h := mul_pow_le hp hq m
  rw [pow_mul]
  apply (lt_div_iff₀ (by positivity : (0:ℝ)<128*((m:ℝ)+1))).mpr
  nlinarith

/-- Strict triangle inputs after choosing c to be a maximum coefficient. -/
structure Data where
  a : ℝ
  b : ℝ
  c : ℝ
  a_pos : 0<a
  b_pos : 0<b
  c_pos : 0<c
  a_le_c : a≤c
  b_le_c : b≤c
  c_lt_sum : c<a+b

namespace Data
variable (d : Data)
def mu : ℝ := d.a+d.b
def nu : ℝ := d.b-d.a
def ratio : ℝ := d.c/d.mu

theorem mu_pos : 0<d.mu := add_pos d.a_pos d.b_pos
theorem ratio_pos : 0<d.ratio := div_pos d.c_pos d.mu_pos
theorem ratio_lt_one : d.ratio<1 := (div_lt_one d.mu_pos).mpr d.c_lt_sum

/-- The maximum choice gives a strict second-order suppression of the odd mode. -/
theorem abs_nu_ratio_lt : |d.nu/d.mu|<d.ratio^2 := by
  have ha2 : 0<d.a^2 := sq_pos_of_pos d.a_pos
  have hb2 : 0<d.b^2 := sq_pos_of_pos d.b_pos
  have hac : d.a^2≤d.c^2 := pow_le_pow_left₀ d.a_pos.le d.a_le_c 2
  have hbc : d.b^2≤d.c^2 := pow_le_pow_left₀ d.b_pos.le d.b_le_c 2
  have hh : |d.mu*d.nu|<d.c^2 := by
    apply abs_lt.mpr
    dsimp [mu,nu]
    constructor <;> nlinarith
  have hm := d.mu_pos
  have hm2 : 0<d.mu^2 := sq_pos_of_pos hm
  have hid : |d.nu/d.mu| *d.mu^2=|d.mu*d.nu| := by
    rw [abs_div,abs_of_pos hm,abs_mul,abs_of_pos hm]
    field_simp
  have hrid : d.ratio^2*d.mu^2=d.c^2 := by
    dsimp [ratio]
    field_simp
  apply (mul_lt_mul_iff_of_pos_right hm2).mp
  rw [hid,hrid]
  exact hh

/-- The chosen multiplier is signature data rather than an input-time search. -/
def constant : ℕ := Classical.choose (exists_even_damping d.ratio_pos d.ratio_lt_one)
theorem constant_spec : 0<d.constant ∧ Even d.constant ∧ d.ratio^d.constant<1/256 :=
  Classical.choose_spec (exists_even_damping d.ratio_pos d.ratio_lt_one)
def length (m : ℕ) : ℕ := d.constant*(m+1)
theorem length_pos (m : ℕ) : 0<d.length m := Nat.mul_pos d.constant_spec.1 (by omega)
theorem length_even (m : ℕ) : Even (d.length m) := d.constant_spec.2.1.mul_right _
theorem length_linear (m : ℕ) : d.length m=d.constant*m+d.constant := by simp [length,Nat.mul_add]
def epsilon (m : ℕ) : ℝ := d.ratio^(d.length m)
def delta (m : ℕ) : ℝ := (d.nu/d.mu)^(d.length m)

theorem epsilon_bounds (m : ℕ) : 0<d.epsilon m ∧
    d.epsilon m<1/(128*((m:ℝ)+1)) :=
  epsilon_small d.ratio_pos d.constant_spec.2.2 m

theorem delta_bounds (m : ℕ) : 0≤d.delta m ∧ d.delta m<(d.epsilon m)^2 := by
  refine ⟨(d.length_even m).pow_nonneg _,?_⟩
  have h := pow_lt_pow_left₀ d.abs_nu_ratio_lt (abs_nonneg (d.nu/d.mu))
    (Nat.ne_of_gt (d.length_pos m))
  rw [(d.length_even m).pow_abs] at h
  simpa only [delta,epsilon,←pow_mul, Nat.mul_comm] using h

/-- Uniform finite-grid separation for every input size, including zero. -/
theorem coefficients_ne (m : ℕ) {i j : ℕ} (hij : i + j ≤ m) (hpos : 0 < i + j) :
    (PositiveDynamicNormalized.A (d.delta m))^(i+j)≠
    (PositiveDynamicNormalized.B (d.delta m)+d.epsilon m)^i*
    (PositiveDynamicNormalized.B (d.delta m)-d.epsilon m)^j :=
  PositiveDynamicNormalized.coefficients_ne (d.epsilon_bounds m).1 (d.epsilon_bounds m).2
    (d.delta_bounds m).1 (d.delta_bounds m).2 hij hpos

end Data
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicParameters
