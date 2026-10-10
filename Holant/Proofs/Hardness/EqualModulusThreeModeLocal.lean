import Holant.Proofs.Hardness.FiniteCapLocal
import Holant.Proofs.Hardness.ThreeModeAnnihilator

/-! The one finite original-field test closes the equality cases. A smaller
secondary modulus excludes all grid points with positive secondary exponent;
the remaining points are excluded by the finite torsion-exponent test. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeLocal
namespace A
export ThreeModeAnnihilator (mode unwanted mem_unwanted denominator polynomial_eval)
end A
variable {K : Type} [NormedField K] [Algebra ℚ K] [FiniteDimensional ℚ K]
local instance : CharZero K := algebraRat.charZero K

def exponent : ℕ := Holant.Projective.BoundedTorsion.torsionExponent (Module.finrank ℚ K)
theorem exponent_pos : 0 < exponent (K:=K) :=
  Holant.Projective.BoundedTorsion.torsionExponent_pos _

/-- All positive resonances follow from the single test in the original field. -/
theorem infinite_of_test (r : K) (h : r ^ exponent (K:=K) ≠ 1) :
    ∀n : ℕ, 0<n → r^n≠1 := FiniteCapLocal.finite_iff_no_resonance r |>.mp h

omit [Algebra ℚ K] [FiniteDimensional ℚ K] in
theorem desired_ne_mode_plus (c mu nu : K) (hc : c≠0)
    (he : ‖mu‖=‖c‖) (hlt : ‖nu‖<‖c‖)
    (hinf : ∀n : ℕ, 0<n → (mu/c)^n≠1)
    (m : ℕ) {ij : ℕ×ℕ} (hij : ij∈A.unwanted m) :
    c^m≠A.mode m c mu nu ij := by
  rcases ij with ⟨i,j⟩
  obtain ⟨hs,hpos⟩ := A.mem_unwanted.mp hij
  intro h
  have hcancel : c^(i+j)=mu^i*nu^j := by
    apply mul_left_cancel₀ (pow_ne_zero (m-i-j) hc)
    rw [←pow_add,show m-i-j+(i+j)=m by omega]
    simpa only [A.mode,mul_assoc] using h
  by_cases hj : j=0
  · subst j
    have hp : mu^i=c^i := by simpa using hcancel.symm
    apply hinf i (by omega)
    rw [div_pow,hp,div_self (pow_ne_zero _ hc)]
  · have hn := congrArg norm hcancel
    simp only [norm_pow,norm_mul,he,pow_add] at hn
    have hp := mul_lt_mul_of_pos_left
      (pow_lt_pow_left₀ hlt (norm_nonneg nu) hj) (pow_pos (norm_pos_iff.mpr hc) i)
    exact (ne_of_lt hp) hn.symm

omit [Algebra ℚ K] [FiniteDimensional ℚ K] in
theorem desired_ne_mode_minus (c mu nu : K) (hc : c≠0)
    (he : ‖nu‖=‖c‖) (hlt : ‖mu‖<‖c‖)
    (hinf : ∀n : ℕ, 0<n → (nu/c)^n≠1)
    (m : ℕ) {ij : ℕ×ℕ} (hij : ij∈A.unwanted m) :
    c^m≠A.mode m c mu nu ij := by
  rcases ij with ⟨i,j⟩
  have hswap : (j,i)∈A.unwanted m := by
    rw [A.mem_unwanted] at hij ⊢
    omega
  have h := desired_ne_mode_plus c nu mu hc he hlt hinf m hswap
  have hm : A.mode m c nu mu (j,i)=A.mode m c mu nu (i,j) := by
    simp only [A.mode]
    rw [show m-j-i=m-i-j by omega]
    ring
  rwa [hm] at h

theorem denominator_plus (a b c : K) (hc : c≠0)
    (he : ‖a+b‖=‖c‖) (hlt : ‖b-a‖<‖c‖)
    (htest : ((a+b)/c)^exponent (K:=K)≠1) (m : ℕ) :
    A.denominator m c (a+b) (b-a)≠0 := by
  apply mul_ne_zero (pow_ne_zero m hc)
  rw [A.polynomial_eval]
  exact Finset.prod_ne_zero_iff.mpr (fun ij hij=>sub_ne_zero.mpr
    (desired_ne_mode_plus c (a+b) (b-a) hc he hlt (infinite_of_test _ htest) m hij))

theorem denominator_minus (a b c : K) (hc : c≠0)
    (he : ‖b-a‖=‖c‖) (hlt : ‖a+b‖<‖c‖)
    (htest : ((b-a)/c)^exponent (K:=K)≠1) (m : ℕ) :
    A.denominator m c (a+b) (b-a)≠0 := by
  apply mul_ne_zero (pow_ne_zero m hc)
  rw [A.polynomial_eval]
  exact Finset.prod_ne_zero_iff.mpr (fun ij hij=>sub_ne_zero.mpr
    (desired_ne_mode_minus c (a+b) (b-a) hc he hlt (infinite_of_test _ htest) m hij))

omit [FiniteDimensional ℚ K] in
theorem powered_sides_nonzero (mu nu : K) (n : ℕ) (hn : 0<n)
    (h : ‖nu‖<‖mu‖ ∨ ‖mu‖<‖nu‖) :
    (mu^n-nu^n)/2≠0 ∧ (mu^n+nu^n)/2≠0 := by
  have hnorm : ‖mu^n‖≠‖nu^n‖ := by
    simp only [norm_pow]
    rcases h with h|h
    · exact ne_of_gt (pow_lt_pow_left₀ h (norm_nonneg nu) (by omega))
    · exact ne_of_lt (pow_lt_pow_left₀ h (norm_nonneg mu) (by omega))
  constructor
  · apply div_ne_zero _ (by norm_num)
    exact sub_ne_zero.mpr (fun h=>hnorm (congrArg norm h))
  · apply div_ne_zero _ (by norm_num)
    intro h
    have hp : mu^n= -(nu^n) := eq_neg_of_add_eq_zero_left h
    exact hnorm (by rw [hp,norm_neg])

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeLocal
