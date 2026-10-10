import Holant.Proofs.Hardness.ThreeModeAnnihilatorExtraction

/-! A list-oriented difference filter suitable for sequential evaluation on a
finite array of actual oracle answers. The roots may be enumerated in any order. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeAnnihilator
open scoped BigOperators
section Algebra
variable {K : Type*} [Field K]

/-- A physical implementation repeatedly replaces adjacent entries by their
shifted difference; this definition deliberately uses that same left order. -/
def differenceFilter : List K → (ℕ → K) → ℕ → K
  | [], values, k => values k
  | r :: rs, values, k => differenceFilter rs (fun j => values (j+1) - r*values j) k

@[simp] theorem differenceFilter_nil (values : ℕ → K) (k : ℕ) :
    differenceFilter [] values k = values k := rfl

@[simp] theorem differenceFilter_cons (r : K) (rs : List K) (values : ℕ → K) (k : ℕ) :
    differenceFilter (r::rs) values k =
      differenceFilter rs (fun j => values (j+1) - r*values j) k := rfl

theorem differenceFilter_congr (roots : List K) {values values' : ℕ → K} (k : ℕ)
    (h : ∀ j, k ≤ j → j ≤ k+roots.length → values j = values' j) :
    differenceFilter roots values k = differenceFilter roots values' k := by
  induction roots generalizing values values' with
  | nil => exact h k le_rfl (by simp)
  | cons r rs ih =>
      apply ih
      intro j hj hj'
      rw [h (j+1) (by omega) (by simpa using (by omega : j+1 ≤ k+(rs.length+1))),
        h j hj (by simp only [List.length_cons]; omega)]

theorem differenceFilter_mul (roots : List K) (z : K) (values : ℕ → K) (k : ℕ) :
    differenceFilter roots (fun j => z * values j) k = z * differenceFilter roots values k := by
  induction roots generalizing values with
  | nil => rfl
  | cons r rs ih =>
      simp only [differenceFilter_cons]
      have he : (fun j => z*values (j+1) - r*(z*values j)) =
          (fun j => z*(values (j+1)-r*values j)) := by funext j; ring
      rw [he, ih]

theorem differenceFilter_sum {ι : Type*} (roots : List K) (s : Finset ι)
    (values : ι → ℕ → K) (k : ℕ) :
    differenceFilter roots (fun j => ∑ a ∈ s, values a j) k =
      ∑ a ∈ s, differenceFilter roots (values a) k := by
  induction roots generalizing values with
  | nil => rfl
  | cons r rs ih =>
      simp only [differenceFilter_cons]
      simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact ih _

/-- The response at a single spectral mode is its moment times the root product. -/
theorem differenceFilter_moment (roots : List K) (t : K) (k : ℕ) :
    differenceFilter roots (fun j => t^(j+1)) k =
      t^(k+1) * (roots.map (fun r => t-r)).prod := by
  induction roots with
  | nil => simp
  | cons r rs ih =>
      rw [differenceFilter_cons]
      have he : (fun j => t^(j+1+1) - r*t^(j+1)) =
          (fun j => (t-r)*t^(j+1)) := by funext j; rw [pow_succ]; ring
      rw [he, differenceFilter_mul, ih]
      simp only [List.map_cons, List.prod_cons]
      ring

/-- This generic finite expansion works directly with assignments, without
first combining equal modes or removing repeated roots. -/
theorem differenceFilter_moments {ι : Type*} (roots : List K) (s : Finset ι)
    (c t : ι → K) (k : ℕ) :
    differenceFilter roots (fun j => ∑ a ∈ s, c a * (t a)^(j+1)) k =
      ∑ a ∈ s, c a * ((t a)^(k+1) * (roots.map (fun r => t a-r)).prod) := by
  rw [differenceFilter_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [differenceFilter_mul, differenceFilter_moment]

/-- Any duplicate-free enumeration of multiplicity pairs gives the same
polynomial product, even when its resulting roots are repeated. -/
theorem enumerated_product (m : ℕ) (lam mu nu : K) (indices : List (ℕ × ℕ))
    (hn : indices.Nodup) (hs : indices.toFinset = unwanted m) (t : K) :
    ((indices.map (mode m lam mu nu)).map (fun r => t-r)).prod =
      (polynomial m lam mu nu).eval t := by
  rw [List.map_map, polynomial_eval, ← hs]
  exact (List.prod_toFinset _ hn).symm

/-- A machine may use any explicit enumeration of the unwanted grid. -/
theorem differenceFilter_sample (m : ℕ) (lam mu nu : K) (indices : List (ℕ × ℕ))
    (hn : indices.Nodup) (hs : indices.toFinset = unwanted m) (c : ℕ × ℕ → K) :
    differenceFilter (indices.map (mode m lam mu nu)) (sample m lam mu nu c) 0 =
      c (0,0) * denominator m lam mu nu := by
  unfold sample
  rw [differenceFilter_moments]
  simp_rw [enumerated_product m lam mu nu indices hn hs]
  simp only [zero_add, pow_one]
  rw [Finset.sum_eq_single (0,0)]
  · rw [mode_zero]
    rfl
  · intro a ha hne
    have hu : a ∈ unwanted m := Finset.mem_erase.mpr ⟨hne,ha⟩
    rw [polynomial_eval_mode_eq_zero m lam mu nu hu, mul_zero, mul_zero]
  · exact fun h => (h (zero_mem_grid m)).elim

/-- Enumerations require exactly one more input sample than there are factors. -/
theorem enumerated_length (m : ℕ) (indices : List (ℕ × ℕ))
    (hn : indices.Nodup) (hs : indices.toFinset = unwanted m) :
    indices.length = (unwanted m).card := by
  rw [← hs, List.toFinset_card_of_nodup hn]

end Algebra
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeAnnihilator
