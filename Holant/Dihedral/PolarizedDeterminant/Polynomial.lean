import Holant.Polynomial.GridInterpolation
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Exact square-monomial coefficients of the physical polarization sums. -/
noncomputable section
namespace Holant.Dihedral.PolarizedDeterminant
open scoped BigOperators
open MvPolynomial

abbrev Cube (s : ℕ) := Fin s → Bool

def exponent {s : ℕ} (z : Cube s) : Fin s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => if z j then 1 else 0)

@[simp] theorem exponent_apply {s : ℕ} (z : Cube s) (j : Fin s) :
    exponent z j = if z j then 1 else 0 := by simp [exponent]

theorem exponent_double_unique {s : ℕ} (x y z : Cube s) :
    exponent x + exponent y = exponent z + exponent z ↔ x = z ∧ y = z := by
  constructor
  · intro h
    have hbit (j : Fin s) : x j = z j ∧ y j = z j := by
      have hj := congrArg (fun e : Fin s →₀ ℕ => e j) h
      simp only [Finsupp.add_apply, exponent_apply] at hj
      cases hx : x j <;> cases hy : y j <;> cases hz : z j <;> simp_all
    exact ⟨funext (fun j => (hbit j).1), funext (fun j => (hbit j).2)⟩
  · rintro ⟨rfl, rfl⟩; rfl

def cubePolynomial {s : ℕ} (S : Finset (Cube s)) (f : Cube s → ℂ) :
    MvPolynomial (Fin s) ℂ := ∑ z ∈ S, monomial (exponent z) (f z)

theorem cubePolynomial_degree {s : ℕ} (S : Finset (Cube s))
    (f : Cube s → ℂ) (j : Fin s) : (cubePolynomial S f).degreeOf j ≤ 1 := by
  classical
  apply (degreeOf_sum_le j S _).trans
  apply Finset.sup_le
  intro z hz
  by_cases hf : f z = 0
  · simp [hf]
  · rw [degreeOf_monomial_eq _ _ hf, exponent_apply]
    split <;> omega

theorem square_coefficient {s : ℕ} (S : Finset (Cube s)) (f g : Cube s → ℂ)
    (z : Cube s) (hz : z ∈ S) :
    (cubePolynomial S f * cubePolynomial S g).coeff (exponent z + exponent z) =
      f z * g z := by
  classical
  simp only [cubePolynomial, Finset.sum_mul, Finset.mul_sum,
    monomial_mul_monomial, coeff_sum, coeff_monomial, exponent_double_unique]
  simp [ite_and, hz]

theorem difference_products_degree {s : ℕ} (S : Finset (Cube s))
    (a b c d : Cube s → ℂ) (j : Fin s) :
    (cubePolynomial S a * cubePolynomial S b -
      cubePolynomial S c * cubePolynomial S d).degreeOf j ≤ 2 := by
  apply (degreeOf_sub_le j _ _).trans
  apply max_le
  · exact (degreeOf_mul_le j _ _).trans (by
      have := cubePolynomial_degree S a j
      have := cubePolynomial_degree S b j
      omega)
  · exact (degreeOf_mul_le j _ _).trans (by
      have := cubePolynomial_degree S c j
      have := cubePolynomial_degree S d j
      omega)

/-- The literal phase monomial, including the two coordinates whose exponent is zero. -/
def phaseMonomial {s : ℕ} (lam : Fin s → ℂ) (z : Cube s) : ℂ :=
  ∏ j, lam j ^ (if z j then 1 else 0 : ℕ)

theorem eval_cubePolynomial {s : ℕ} (S : Finset (Cube s)) (f : Cube s → ℂ)
    (lam : Fin s → ℂ) :
    eval lam (cubePolynomial S f) = ∑ z ∈ S, phaseMonomial lam z * f z := by
  classical
  simp only [cubePolynomial, map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finsupp.prod_fintype]
  · simp [phaseMonomial, mul_comm]
  · intro j; simp

end Holant.Dihedral.PolarizedDeterminant
