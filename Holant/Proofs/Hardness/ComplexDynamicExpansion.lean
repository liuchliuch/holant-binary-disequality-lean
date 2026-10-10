import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Elementary finite-product estimates used for complex dynamic separation.
All estimates are finite algebraic inductions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicExpansion

theorem norm_sum_le_length_mul (l : List ℂ) {s : ℝ} (_hs : 0 ≤ s)
    (hl : ∀ u ∈ l, ‖u‖ ≤ s) : ‖l.sum‖ ≤ (l.length : ℝ) * s := by
  induction l with
  | nil => simp
  | cons u l ih =>
    have hu := hl u (by simp)
    have ht := ih (fun v hv => hl v (by simp [hv]))
    calc
      ‖(u :: l).sum‖ = ‖u + l.sum‖ := by simp
      _ ≤ ‖u‖ + ‖l.sum‖ := norm_add_le _ _
      _ ≤ ((u :: l).length : ℝ) * s := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; linarith

/-- A quadratic first-order remainder, uniform over arbitrary complex phases. -/
theorem product_remainder (l : List ℂ) {s : ℝ} (hs : 0 ≤ s)
    (hl : ∀ u ∈ l, ‖u‖ ≤ s) (hsmall : (l.length : ℝ) * s ≤ 1) :
    ‖(l.map (fun u => 1 + u)).prod - 1 - l.sum‖ ≤ (l.length : ℝ)^2 * s^2 := by
  induction l with
  | nil => simp
  | cons u l ih =>
    have hu := hl u (by simp)
    have ht : ∀ v ∈ l, ‖v‖ ≤ s := fun v hv => hl v (by simp [hv])
    have hn : 0 ≤ (l.length : ℝ) := Nat.cast_nonneg _
    have hsmall' : (l.length : ℝ) * s ≤ 1 := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hsmall
      nlinarith
    have he := ih ht hsmall'
    have hlSum := norm_sum_le_length_mul l hs ht
    have hnu : ‖1 + u‖ ≤ 1 + s := by simpa using (norm_add_le (1 : ℂ) u).trans (by simpa using hu)
    have hid : ((u :: l).map (fun v => 1 + v)).prod - 1 - (u :: l).sum =
        ((l.map (fun v => 1 + v)).prod - 1 - l.sum) * (1 + u) + l.sum * u := by
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      ring
    rw [hid]
    calc
      _ ≤ ‖(l.map (fun v => 1 + v)).prod - 1 - l.sum‖ * ‖1 + u‖ + ‖l.sum‖ * ‖u‖ := by
        simpa only [norm_mul] using norm_add_le
          (((l.map (fun v => 1 + v)).prod - 1 - l.sum) * (1 + u)) (l.sum * u)
      _ ≤ (l.length : ℝ)^2 * s^2 * (1 + s) + ((l.length : ℝ) * s) * s := by
        exact add_le_add (mul_le_mul he hnu (norm_nonneg _) (by positivity))
          (mul_le_mul hlSum hu (norm_nonneg _) (by positivity))
      _ ≤ ((u :: l).length : ℝ)^2 * s^2 := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        have hh := mul_le_mul_of_nonneg_left hsmall' (show 0 ≤ (l.length : ℝ) * s^2 by positivity)
        nlinarith [sq_nonneg s]

/-- The first-order error for a power. -/
theorem power_remainder (u : ℂ) (n : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (hu : ‖u‖ ≤ s) (hsmall : (n : ℝ) * s ≤ 1) :
    ‖(1 + u)^n - 1 - (n : ℂ) * u‖ ≤ (n : ℝ)^2 * s^2 := by
  have h := product_remainder (List.replicate n u) hs
    (fun v hv => by rcases List.mem_replicate.mp hv with ⟨_, rfl⟩; exact hu) (by simpa using hsmall)
  simpa using h

/-- The first-order error for two powers with a common smallness budget. -/
theorem mixed_remainder (u v : ℂ) (i j : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (hu : ‖u‖ ≤ s) (hv : ‖v‖ ≤ s) (hsmall : ((i+j : ℕ) : ℝ) * s ≤ 1) :
    ‖(1 + u)^i * (1 + v)^j - 1 - ((i : ℂ)*u + (j : ℂ)*v)‖ ≤
      ((i+j : ℕ) : ℝ)^2 * s^2 := by
  have h := product_remainder (List.replicate i u ++ List.replicate j v) hs
    (fun z hz => by
      rcases List.mem_append.mp hz with h | h
      · rcases List.mem_replicate.mp h with ⟨_, rfl⟩; exact hu
      · rcases List.mem_replicate.mp h with ⟨_, rfl⟩; exact hv)
    (by simpa using hsmall)
  simpa [List.map_append, List.prod_append, List.sum_append] using h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicExpansion
