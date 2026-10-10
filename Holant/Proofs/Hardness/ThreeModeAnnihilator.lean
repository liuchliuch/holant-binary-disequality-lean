import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic

/-!
A finite annihilator for three spectral modes. Repeated unwanted eigenvalues are
kept as repeated factors, and zero eigenvalues require no exceptional branch.
The analytic hypotheses are used only to show that the desired eigenvalue is
not an unwanted one; all coefficient identities are finite polynomial algebra.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeAnnihilator
open scoped BigOperators
open Polynomial

/-- The triangular grid of multiplicities of the two unwanted modes. -/
def grid (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)).product (Finset.range (m + 1))).filter
    (fun a => a.1 + a.2 ≤ m)

@[simp] theorem mem_grid {m i j : ℕ} : (i,j) ∈ grid m ↔ i + j ≤ m := by
  simp [grid]
  omega

@[simp] theorem zero_mem_grid (m : ℕ) : (0,0) ∈ grid m := by simp

/-- Every grid point except the desired all-first-mode point. -/
def unwanted (m : ℕ) : Finset (ℕ × ℕ) := (grid m).erase (0,0)

@[simp] theorem mem_unwanted {m i j : ℕ} :
    (i,j) ∈ unwanted m ↔ i + j ≤ m ∧ 0 < i + j := by
  simp [unwanted]
  omega

@[simp] theorem unwanted_zero : unwanted 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨hij,hpos⟩ := mem_unwanted.mp ha
  omega

theorem unwanted_card_le (m : ℕ) : (unwanted m).card ≤ (m + 1)^2 := by
  calc
    (unwanted m).card ≤ (grid m).card := Finset.card_le_card (Finset.erase_subset _ _)
    _ ≤ ((Finset.range (m+1)).product (Finset.range (m+1))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = (m+1)^2 := by simp [pow_two]

section Algebra
variable {K : Type*} [Field K]

/-- Eigenvalue of a length-one spectral sample at a multiplicity grid point. -/
def mode (m : ℕ) (lam mu nu : K) (a : ℕ × ℕ) : K :=
  lam^(m-a.1-a.2) * mu^a.1 * nu^a.2

@[simp] theorem mode_zero (m : ℕ) (lam mu nu : K) : mode m lam mu nu (0,0) = lam^m := by
  simp [mode]

/-- Factors are indexed by multiplicities, not by distinct roots. -/
def polynomial (m : ℕ) (lam mu nu : K) : K[X] :=
  ∏ a ∈ unwanted m, (X - C (mode m lam mu nu a))

@[simp] theorem polynomial_zero (lam mu nu : K) : polynomial 0 lam mu nu = 1 := by
  simp [polynomial]

theorem polynomial_monic (m : ℕ) (lam mu nu : K) : (polynomial m lam mu nu).Monic := by
  exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

/-- In particular, no distinctness assumption is needed for the degree. -/
theorem polynomial_natDegree (m : ℕ) (lam mu nu : K) :
    (polynomial m lam mu nu).natDegree = (unwanted m).card := by
  rw [polynomial, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp

theorem polynomial_natDegree_le (m : ℕ) (lam mu nu : K) :
    (polynomial m lam mu nu).natDegree ≤ (m+1)^2 := by
  rw [polynomial_natDegree]
  exact unwanted_card_le m

theorem polynomial_eval (m : ℕ) (lam mu nu t : K) :
    (polynomial m lam mu nu).eval t = ∏ a ∈ unwanted m, (t - mode m lam mu nu a) := by
  simp [polynomial, eval_prod]

theorem polynomial_eval_mode_eq_zero (m : ℕ) (lam mu nu : K) {a : ℕ × ℕ}
    (ha : a ∈ unwanted m) :
    (polynomial m lam mu nu).eval (mode m lam mu nu a) = 0 := by
  rw [polynomial_eval]
  exact Finset.prod_eq_zero ha (sub_self _)

/-- The degree-dependent query count is already polynomially bounded. -/
def queryCount (m : ℕ) (lam mu nu : K) : ℕ := (polynomial m lam mu nu).natDegree + 1

theorem queryCount_eq_card (m : ℕ) (lam mu nu : K) :
    queryCount m lam mu nu = (unwanted m).card+1 := by
  simp [queryCount, polynomial_natDegree]

theorem queryCount_le (m : ℕ) (lam mu nu : K) : queryCount m lam mu nu ≤ (m+1)^2+1 :=
  Nat.add_le_add_right (polynomial_natDegree_le m lam mu nu) 1

/-- Samples start at exponent one, so a zero unwanted root is annihilated too. -/
def filterValue (m : ℕ) (lam mu nu t : K) : K :=
  ∑ k ∈ Finset.range (queryCount m lam mu nu), (polynomial m lam mu nu).coeff k * t^(k+1)

theorem filterValue_eq (m : ℕ) (lam mu nu t : K) :
    filterValue m lam mu nu t = t * (polynomial m lam mu nu).eval t := by
  rw [filterValue, eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_succ]
  ring

theorem filterValue_mode_eq_zero (m : ℕ) (lam mu nu : K) {a : ℕ × ℕ}
    (ha : a ∈ unwanted m) : filterValue m lam mu nu (mode m lam mu nu a) = 0 := by
  rw [filterValue_eq, polynomial_eval_mode_eq_zero m lam mu nu ha, mul_zero]

@[simp] theorem filterValue_zero (lam mu nu t : K) : filterValue 0 lam mu nu t = t := by
  simp [filterValue_eq]

/-- The nonzero normalization needed by interpolation. -/
def denominator (m : ℕ) (lam mu nu : K) : K :=
  lam^m * (polynomial m lam mu nu).eval (lam^m)

theorem filterValue_desired (m : ℕ) (lam mu nu : K) :
    filterValue m lam mu nu (lam^m) = denominator m lam mu nu := filterValue_eq m lam mu nu _

@[simp] theorem denominator_zero (lam mu nu : K) : denominator 0 lam mu nu = 1 := by
  simp [denominator]

end Algebra

section Normed
variable {K : Type*} [NormedField K]

/-- Strict dominance excludes resonance on every nonzero triangular-grid point.
This proof does not assume nonzero secondary modes or distinct unwanted roots. -/
theorem mode_norm_lt {m i j : ℕ} {lam mu nu : K}
    (hmu : ‖mu‖ < ‖lam‖) (hnu : ‖nu‖ < ‖lam‖)
    (hij : i+j ≤ m) (hpos : 0 < i+j) :
    ‖mode m lam mu nu (i,j)‖ < ‖lam^m‖ := by
  have hlam : 0 < ‖lam‖ := lt_of_le_of_lt (norm_nonneg mu) hmu
  have hsmall : ‖mu‖^i * ‖nu‖^j < ‖lam‖^(i+j) := by
    rw [pow_add]
    by_cases hi : i = 0
    · subst i
      simpa using pow_lt_pow_left₀ hnu (norm_nonneg nu) (by omega : j ≠ 0)
    · calc
        ‖mu‖^i * ‖nu‖^j ≤ ‖mu‖^i * ‖lam‖^j :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg nu) hnu.le j)
            (pow_nonneg (norm_nonneg mu) i)
        _ < ‖lam‖^i * ‖lam‖^j :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hmu (norm_nonneg mu) hi) (pow_pos hlam j)
  have he : m-i-j+(i+j) = m := by omega
  calc
    ‖mode m lam mu nu (i,j)‖ = ‖lam‖^(m-i-j) * (‖mu‖^i * ‖nu‖^j) := by
      simp [mode, norm_mul, norm_pow, mul_assoc]
    _ < ‖lam‖^(m-i-j) * ‖lam‖^(i+j) := mul_lt_mul_of_pos_left hsmall (pow_pos hlam _)
    _ = ‖lam^m‖ := by rw [← pow_add, he, norm_pow]

theorem desired_ne_mode {m : ℕ} {lam mu nu : K}
    (hmu : ‖mu‖ < ‖lam‖) (hnu : ‖nu‖ < ‖lam‖) {a : ℕ × ℕ}
    (ha : a ∈ unwanted m) : lam^m ≠ mode m lam mu nu a := by
  rcases a with ⟨i,j⟩
  obtain ⟨hij,hpos⟩ := mem_unwanted.mp ha
  intro heq
  have hlt := mode_norm_lt hmu hnu hij hpos
  rw [← heq] at hlt
  exact (lt_irrefl _) hlt

theorem polynomial_eval_desired_ne_zero {m : ℕ} {lam mu nu : K}
    (hmu : ‖mu‖ < ‖lam‖) (hnu : ‖nu‖ < ‖lam‖) :
    (polynomial m lam mu nu).eval (lam^m) ≠ 0 := by
  rw [polynomial_eval]
  exact Finset.prod_ne_zero_iff.mpr (fun a ha => sub_ne_zero.mpr (desired_ne_mode hmu hnu ha))

/-- Strict dominance itself implies lam ≠ 0. -/
theorem dominant_ne_zero {lam mu : K} (hmu : ‖mu‖ < ‖lam‖) : lam ≠ 0 := by
  intro hlam
  simp only [hlam, norm_zero] at hmu
  exact (not_lt_of_ge (norm_nonneg mu)) hmu

theorem denominator_ne_zero {m : ℕ} {lam mu nu : K}
    (hmu : ‖mu‖ < ‖lam‖) (hnu : ‖nu‖ < ‖lam‖) : denominator m lam mu nu ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (dominant_ne_zero hmu)) (polynomial_eval_desired_ne_zero hmu hnu)

end Normed
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeAnnihilator
