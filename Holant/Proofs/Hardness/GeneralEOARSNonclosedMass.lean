import Holant.Proofs.Hardness.GeneralEOARSSupport
import Holant.Proofs.Hardness.GeneralEODEQProducerSupportBasic

/-! A fixed-weight nonzero distribution cannot have nonnegative correlations
between every pair of distinct coordinates. This finite mass identity is used
only to select a pair of original ports; it asserts no gadget availability. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedMass
open Holant
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def spin (b : Bool) : ℝ := if b then 1 else -1

theorem spin_sq (b : Bool) : spin b * spin b = 1 := by
  cases b <;> norm_num [spin]

theorem charge_sum (x : Fin n → Bool) : (charge x : ℝ) = ∑ i, spin (x i) := by
  have hb (b : Bool) : spin b = 2 * (if b then (1 : ℝ) else 0) - 1 := by
    cases b <;> norm_num [spin]
  simp only [hb, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [charge, weight, Nat.cast_sum, Int.cast_sub]

def correlation (μ : (Fin n → Bool) → ℝ) (i j : Fin n) : ℝ :=
  ∑ x, μ x * spin (x i) * spin (x j)

theorem diagonal (μ : (Fin n → Bool) → ℝ) (i : Fin n) :
    correlation μ i i = ∑ x, μ x := by
  simp only [correlation, mul_assoc, spin_sq, mul_one]

theorem row_sum (μ : (Fin n → Bool) → ℝ)
    (central : ∀ x, μ x ≠ 0 → charge x = 0) (i : Fin n) :
    ∑ j, correlation μ i j = 0 := by
  unfold correlation
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  rw [← Finset.mul_sum, ← charge_sum]
  by_cases hx : μ x = 0
  · simp [hx]
  · rw [central x hx]
    simp

/-- For every fixed port, a distinct port has strictly negative correlation.
In particular, uniform pair marginals on every pair are impossible. -/
theorem negative_pair (μ : (Fin n → Bool) → ℝ)
    (central : ∀ x, μ x ≠ 0 → charge x = 0)
    (positive : 0 < ∑ x, μ x) (i : Fin n) :
    ∃ j, j ≠ i ∧ correlation μ i j < 0 := by
  by_contra hn
  have nonneg : ∀ j, 0 ≤ correlation μ i j := by
    intro j
    by_cases hj : j = i
    · subst j
      rw [diagonal]
      exact positive.le
    · exact le_of_not_gt (fun h => hn ⟨j,hj,h⟩)
  have hsum : 0 < ∑ j, correlation μ i j := by
    apply Finset.sum_pos'
    · intro j _
      exact nonneg j
    · exact ⟨i,Finset.mem_univ i,by simpa only [diagonal] using positive⟩
  rw [row_sum μ central i] at hsum
  exact lt_irrefl 0 hsum

def mass (f : Signature ℂ n) (x : Fin n → Bool) : ℝ := ‖f x‖ ^ 2

theorem mass_positive (f : Signature ℂ n) (hn : f ≠ 0) :
    0 < ∑ x, mass f x := by
  classical
  obtain ⟨x,hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hh
    apply hn
    funext x
    exact not_ne_iff.mp (fun hx => hh ⟨x,hx⟩)
  apply Finset.sum_pos'
  · intro y _
    exact sq_nonneg _
  · exact ⟨x,Finset.mem_univ x,sq_pos_of_pos (norm_pos_iff.mpr hx)⟩

theorem mass_central (f : Signature ℂ n) (he : Signature.CentralSupport f) :
    ∀ x, mass f x ≠ 0 → charge x = 0 := by
  intro x hx
  have hf : f x ≠ 0 := by
    intro hz
    exact hx (by simp [mass,hz])
  have hw : 2 * weight x = n := by
    by_contra hw
    exact hf (he x hw)
  unfold charge
  omega

theorem signature_negative_pair (f : Signature ℂ n)
    (he : Signature.CentralSupport f) (hn : f ≠ 0) (i : Fin n) :
    ∃ j, j ≠ i ∧ correlation (mass f) i j < 0 :=
  negative_pair (mass f) (mass_central f he) (mass_positive f hn) i

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedMass
