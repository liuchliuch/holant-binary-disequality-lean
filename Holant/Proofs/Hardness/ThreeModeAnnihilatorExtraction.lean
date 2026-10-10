import Holant.Proofs.Hardness.ThreeModeAnnihilator

/-! Finite coefficient extraction from samples of the three-mode spectrum. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeAnnihilator
open scoped BigOperators

section Algebra
variable {K : Type*} [Field K]

/-- A finite spectral expansion at a positive chain length. -/
def sample (m : ℕ) (lam mu nu : K) (c : ℕ × ℕ → K) (k : ℕ) : K :=
  ∑ a ∈ grid m, c a * (mode m lam mu nu a)^(k+1)

/-- The finite annihilator is applied directly to actual sample values. -/
def extractNumerator (m : ℕ) (lam mu nu : K) (values : ℕ → K) : K :=
  ∑ k ∈ Finset.range (queryCount m lam mu nu), (polynomial m lam mu nu).coeff k * values k

/-- All unwanted multiplicities cancel, with no distinct-root hypothesis. -/
theorem extractNumerator_sample (m : ℕ) (lam mu nu : K) (c : ℕ × ℕ → K) :
    extractNumerator m lam mu nu (sample m lam mu nu c) = c (0,0) * denominator m lam mu nu := by
  have hexpand : extractNumerator m lam mu nu (sample m lam mu nu c) =
      ∑ a ∈ grid m, c a * filterValue m lam mu nu (mode m lam mu nu a) := by
    unfold extractNumerator sample filterValue
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hexpand, Finset.sum_eq_single (0,0)]
  · rw [mode_zero, filterValue_desired]
  · intro a ha hne
    have hu : a ∈ unwanted m := Finset.mem_erase.mpr ⟨hne,ha⟩
    rw [filterValue_mode_eq_zero m lam mu nu hu, mul_zero]
  · exact fun h => (h (zero_mem_grid m)).elim

/-- Congruence only asks for sample correctness at the finitely queried lengths. -/
theorem extractNumerator_congr (m : ℕ) (lam mu nu : K) {values values' : ℕ → K}
    (h : ∀ k < queryCount m lam mu nu, values k = values' k) :
    extractNumerator m lam mu nu values = extractNumerator m lam mu nu values' := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [h k (Finset.mem_range.mp hk)]

end Algebra

section Normed
variable {K : Type*} [NormedField K]

/-- Coefficients for a division-free numerator and one final nonzero division. -/
def extract (m : ℕ) (lam mu nu : K) (values : ℕ → K) : K :=
  extractNumerator m lam mu nu values / denominator m lam mu nu

/-- Exact extraction of the all-first-mode coefficient from positive samples. -/
theorem extract_sample {m : ℕ} {lam mu nu : K}
    (hmu : ‖mu‖ < ‖lam‖) (hnu : ‖nu‖ < ‖lam‖) (c : ℕ × ℕ → K) :
    extract m lam mu nu (sample m lam mu nu c) = c (0,0) := by
  rw [extract, extractNumerator_sample]
  exact mul_div_cancel_right₀ _ (denominator_ne_zero hmu hnu)

/-- The intended consumer theorem: finite actual-query equalities suffice. -/
theorem extract_actual {m : ℕ} {lam mu nu : K}
    (hmu : ‖mu‖ < ‖lam‖) (hnu : ‖nu‖ < ‖lam‖)
    (c : ℕ × ℕ → K) (values : ℕ → K)
    (hvalues : ∀ k < queryCount m lam mu nu, values k = sample m lam mu nu c k) :
    extract m lam mu nu values = c (0,0) := by
  unfold extract
  rw [extractNumerator_congr m lam mu nu hvalues, extractNumerator_sample]
  exact mul_div_cancel_right₀ _ (denominator_ne_zero hmu hnu)

end Normed
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeAnnihilator
