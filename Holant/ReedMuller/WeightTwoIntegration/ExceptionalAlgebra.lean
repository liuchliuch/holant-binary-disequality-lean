import Holant.ReedMuller.CoefficientAtlas.Physical

/-! Exact coefficients of the six-port exceptional two-copy construction.
All scalars in this file are literal complex coefficients. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators

structure ExceptionalData where
  r : Fin 3 → ℂ
  kappa : ℂ
  r_ne_zero : ∀ i, r i ≠ 0
  kappa_ne_zero : kappa ≠ 0
  kappa_ne_one : kappa ≠ 1
  square : ∀ i, kappa * r i ^ 2 = 1

/-- The normalized three-coordinate table of Lemma 7.8. -/
def exceptionalH (r : Fin 3 → ℂ) (k : ℂ) : Bool → Bool → Bool → ℂ
  | false, false, false => 1
  | true, false, false => r 0
  | false, true, false => r 1
  | false, false, true => r 2
  | true, true, false => k * r 0 * r 1
  | true, false, true => k * r 0 * r 2
  | false, true, true => k * r 1 * r 2
  | true, true, true => k * r 0 * r 1 * r 2

namespace ExceptionalData

def h (d : ExceptionalData) := exceptionalH d.r d.kappa
def theta (d : ExceptionalData) : ℂ := d.kappa * d.r 1 * d.r 2
def eta (d : ExceptionalData) : ℂ := -(d.kappa * d.r 0 * d.r 2)
def sigma (d : ExceptionalData) : ℂ := d.kappa * d.r 0 * d.r 1
def coefficient (d : ExceptionalData) : ℂ := 2 * (d.kappa - 1) / d.kappa

theorem pair_square (d : ExceptionalData) (i j : Fin 3) :
    (d.kappa * d.r i * d.r j)^2 = 1 := by
  calc
    _ = (d.kappa * d.r i^2) * (d.kappa * d.r j^2) := by ring
    _ = 1 := by rw [d.square i,d.square j]; ring

theorem theta_square (d : ExceptionalData) : d.theta^2 = 1 := d.pair_square 1 2
theorem eta_square (d : ExceptionalData) : d.eta^2 = 1 := by
  simpa [eta] using d.pair_square 0 2
theorem sigma_square (d : ExceptionalData) : d.sigma^2 = 1 := d.pair_square 0 1

theorem theta_sign (d : ExceptionalData) : d.theta = 1 ∨ d.theta = -1 :=
  sq_eq_one_iff.mp d.theta_square
theorem eta_sign (d : ExceptionalData) : d.eta = 1 ∨ d.eta = -1 :=
  sq_eq_one_iff.mp d.eta_square
theorem sigma_sign (d : ExceptionalData) : d.sigma = 1 ∨ d.sigma = -1 :=
  sq_eq_one_iff.mp d.sigma_square

theorem coefficient_ne_zero (d : ExceptionalData) : d.coefficient ≠ 0 := by
  exact div_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr d.kappa_ne_one))
    d.kappa_ne_zero

/-- The second copy with its internal paired join contributes exactly 2 r₀ᵃ. -/
theorem inner_sum (d : ExceptionalData) (a : Bool) :
    (∑ c : Bool, d.theta ^ (if c then 1 else 0) * d.h a c c) =
      2 * d.r 0 ^ (if a then 1 else 0) := by
  have hh := d.theta_square
  cases a <;> simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false,
    ite_true, pow_zero, pow_one, one_mul, h, exceptionalH]
  · change d.theta * d.theta + 1 = 2 * 1
    linear_combination hh
  · change d.theta * (d.kappa * d.r 0 * d.r 1 * d.r 2) + d.r 0 = 2 * d.r 0
    calc
      _ = d.r 0 * (1 + d.theta^2) := by simp only [theta]; ring
      _ = _ := by rw [hh]; ring

/-- Logical value of the stated two-copy, two-paired-join construction. -/
def Q (d : ExceptionalData) (x y : Bool) : ℂ :=
  ∑ a : Bool, ∑ c : Bool,
    d.eta ^ (if a then 1 else 0) * d.theta ^ (if c then 1 else 0) *
      d.h x y a * d.h a c c

theorem Q_reduced (d : ExceptionalData) (x y : Bool) :
    d.Q x y = 2 * (d.h x y false + d.eta * d.r 0 * d.h x y true) := by
  unfold Q
  have hh (a : Bool) :
      (∑ c : Bool, d.eta ^ (if a then 1 else 0) * d.theta ^ (if c then 1 else 0) *
          d.h x y a * d.h a c c) =
      d.eta ^ (if a then 1 else 0) * d.h x y a *
        (∑ c : Bool, d.theta ^ (if c then 1 else 0) * d.h a c c) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  simp_rw [hh,inner_sum]
  simp
  ring

/-- Exact diagonal answer, including the factor 2 hidden by projective notation. -/
theorem Q_exact (d : ExceptionalData) (x y : Bool) :
    d.Q x y = if x = y then d.coefficient * (if x then d.sigma else 1) else 0 := by
  rw [Q_reduced]
  have hh := d.pair_square 0 2
  cases x <;> cases y <;>
    simp only [h,exceptionalH,eta,sigma,coefficient,Bool.false_eq_true,
      ite_false,ite_true,reduceCtorEq,mul_one]
  · field_simp [d.kappa_ne_zero]
    linear_combination -hh
  · linear_combination -2 * d.r 1 * hh
  · linear_combination -2 * d.r 0 * hh
  · field_simp [d.kappa_ne_zero]
    linear_combination -d.r 0 * d.r 1 * hh

end ExceptionalData
end Holant.ReedMuller.WeightTwoIntegration
