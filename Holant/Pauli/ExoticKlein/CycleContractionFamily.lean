import Holant.Pauli.ExoticKlein.CycleContraction
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Literal Boolean contractions for disjoint cycles indexed by an arbitrary
finite type, and the exact number of their nonzero original-label coefficients. -/

namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators

/-- The actual Boolean tensor contraction of one alternating cycle. -/
def cycleContraction (length : ℕ) (fixed : Fin length → Label)
    (mReverse nReverse : Fin length → Bool) (labels : Fin length → Label) : ℂ :=
  ∑ x : Fin length → Bool, ∑ y : Fin length → Bool,
    ∏ i : Fin length,
      oriented (mReverse i) (dual (labels i)) (x i) (y i) *
        oriented (nReverse i) (E (fixed i)) (y i) (x (finRotate length i))

theorem cycleContraction_succ (n : ℕ) (fixed : Fin (n + 1) → Label)
    (mReverse nReverse : Fin (n + 1) → Bool) (labels : Fin (n + 1) → Label) :
    cycleContraction (n + 1) fixed mReverse nReverse labels =
      cycleCoefficient n fixed mReverse nReverse labels :=
  (cycleCoefficient_eq_sum n fixed mReverse nReverse labels).symm

theorem cycleContraction_support_card (length : ℕ) (hLength : 0 < length)
    (fixed : Fin length → Label) (mReverse nReverse : Fin length → Bool) :
    Fintype.card {labels : Fin length → Label //
      cycleContraction length fixed mReverse nReverse labels ≠ 0} = 4 ^ (length - 1) := by
  cases length with
  | zero => exact (Nat.not_lt_zero _ hLength).elim
  | succ n =>
    simpa only [cycleContraction_succ, Nat.add_sub_cancel] using
      cycle_support_card n fixed mReverse nReverse

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The actual contraction on the disjoint union of the cycles' edge indices.
Every Boolean assignment is summed globally, before any factorization. -/
def cycleFamilyContraction (length : C → ℕ)
    (fixed : (Σ c, Fin (length c)) → Label)
    (mReverse nReverse : (Σ c, Fin (length c)) → Bool)
    (labels : (Σ c, Fin (length c)) → Label) : ℂ :=
  ∑ x : (Σ c, Fin (length c)) → Bool,
    ∑ y : (Σ c, Fin (length c)) → Bool,
      ∏ e : Σ c, Fin (length c),
        oriented (mReverse e) (dual (labels e)) (x e) (y e) *
          oriented (nReverse e) (E (fixed e)) (y e)
            (x ⟨e.1, finRotate (length e.1) e.2⟩)

/-- Finite distributivity and the assignment currying equivalence factor the
global contraction into its independent cycle contractions. -/
theorem cycleFamilyContraction_eq_prod (length : C → ℕ)
    (fixed : (Σ c, Fin (length c)) → Label)
    (mReverse nReverse : (Σ c, Fin (length c)) → Bool)
    (labels : (Σ c, Fin (length c)) → Label) :
    cycleFamilyContraction length fixed mReverse nReverse labels =
      ∏ c, cycleContraction (length c) (fun i => fixed ⟨c, i⟩)
        (fun i => mReverse ⟨c, i⟩) (fun i => nReverse ⟨c, i⟩)
        (fun i => labels ⟨c, i⟩) := by
  classical
  unfold cycleFamilyContraction cycleContraction
  rw [← (Equiv.piCurry (fun c (_ : Fin (length c)) => Bool)).symm.sum_comp]
  simp_rw [← (Equiv.piCurry (fun c (_ : Fin (length c)) => Bool)).symm.sum_comp,
    Fintype.prod_sigma]
  simp only [Equiv.piCurry_symm_apply, Sigma.uncurry]
  symm
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Fintype.prod_sum]

/-- The global nonzero labels are precisely independent choices of a
nonzero local label assignment on every cycle. -/
def cycleFamilyContractionSupportEquiv (length : C → ℕ)
    (fixed : (Σ c, Fin (length c)) → Label)
    (mReverse nReverse : (Σ c, Fin (length c)) → Bool) :
    {labels : (Σ c, Fin (length c)) → Label //
      cycleFamilyContraction length fixed mReverse nReverse labels ≠ 0} ≃
      ((c : C) → {labels : Fin (length c) → Label //
        cycleContraction (length c) (fun i => fixed ⟨c, i⟩)
          (fun i => mReverse ⟨c, i⟩) (fun i => nReverse ⟨c, i⟩) labels ≠ 0}) where
  toFun labels c := ⟨fun i => labels.val ⟨c, i⟩, by
    have h := labels.property
    rw [cycleFamilyContraction_eq_prod] at h
    exact (Finset.prod_ne_zero_iff.mp h) c (Finset.mem_univ c)⟩
  invFun labels := ⟨fun e => (labels e.1).val e.2, by
    rw [cycleFamilyContraction_eq_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun c _ => (labels c).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each nonempty cycle contributes exactly one independent affine constraint
on its original labels. The coefficient here remains the actual Boolean sum. -/
theorem cycleFamilyContraction_support_card (length : C → ℕ)
    (hLength : ∀ c, 0 < length c)
    (fixed : (Σ c, Fin (length c)) → Label)
    (mReverse nReverse : (Σ c, Fin (length c)) → Bool) :
    Fintype.card {labels : (Σ c, Fin (length c)) → Label //
      cycleFamilyContraction length fixed mReverse nReverse labels ≠ 0} =
        4 ^ ((∑ c, length c) - Fintype.card C) := by
  rw [Fintype.card_congr (cycleFamilyContractionSupportEquiv length fixed mReverse nReverse),
    Fintype.card_pi]
  simp_rw [cycleContraction_support_card _ (hLength _)]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simpa using Finset.sum_tsub_distrib Finset.univ
    (f := length) (g := fun _ => 1) (fun c _ => hLength c)

end
end Holant.Pauli.ExoticKlein
