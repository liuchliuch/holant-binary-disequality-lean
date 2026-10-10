import Holant.Proofs.Closure.ClosureRootPencilTriangle

/-! Common support is derived from the full actual root deck. The exceptional
three-root triangle is excluded by supported phase ratios; sampled zeros are
handled through the separate genuine dependence branch. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective

theorem independent_union_even {m : ℕ} (hm : 2 ≤ m) (U V : Signature ℂ 4)
    (independent : ¬ Dependent U V)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    Even (unionSupport U V).card := by
  classical
  obtain ⟨s,t,hs,ht,different⟩ := roots_two hm
  rw [union_eq_two_samples U V s t different]
  apply closed_support_even
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (support_closed
      (independent_root_supports U V independent samples s hs) x hx)
  · exact Finset.mem_union_right _ (support_closed
      (independent_root_supports U V independent samples t ht) x hx)

theorem four_roots_union_le_four {m : ℕ} (hm : 4 ≤ m) (U V : Signature ℂ 4)
    (independent : ¬ Dependent U V)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    (unionSupport U V).card ≤ 4 := by
  letI : NeZero m := ⟨by omega⟩
  have nonzero : ∀ t ∈ Laurent.rootCoset m 1, (fun x => U x+t*V x) ≠ 0 :=
    fun t _ => independent_samples_nonzero independent t
  have exactCard : ∀ t ∈ Laurent.rootCoset m 1,
      (ClosureRootPencilCount.pencilSupport U V t).card=4 := by
    intro t ht
    obtain ⟨D⟩ := independent_root_supports U V independent samples t (root_of_mem ht)
    simpa only [ClosureRootPencilCount.pencilSupport,support,pencil] using D.support_card
  have bound := ClosureRootPencilCount.actual_roots_four_union_le_five m hm U V nonzero exactCard
  obtain ⟨k,hk⟩ := independent_union_even (by omega : 2 ≤ m) U V independent samples
  change (unionSupport U V).card ≤ 5 at bound
  omega

theorem three_roots_union_le_four (U V : Signature ℂ 4)
    (independent : ¬ Dependent U V)
    (samples : ∀ t : ℂ, t^3=1 → pencil U V t=0 ∨ RootProduct 3 (pencil U V t)) :
    (unionSupport U V).card ≤ 4 := by
  classical
  have nonzero : ∀ t ∈ Laurent.rootCoset 3 1, (fun x => U x+t*V x) ≠ 0 :=
    fun t _ => independent_samples_nonzero independent t
  have exactCard : ∀ t ∈ Laurent.rootCoset 3 1,
      (ClosureRootPencilCount.pencilSupport U V t).card=4 := by
    intro t ht
    obtain ⟨D⟩ := independent_root_supports U V independent samples t (root_of_mem ht)
    simpa only [ClosureRootPencilCount.pencilSupport,support,pencil] using D.support_card
  have bound := ClosureRootPencilCount.three_roots_four_union_le_six U V nonzero exactCard
  obtain ⟨k,hk⟩ := independent_union_even (by omega : 2 ≤ 3) U V independent samples
  by_contra large
  have unionSix : (unionSupport U V).card=6 := by
    change (unionSupport U V).card ≤ 6 at bound
    omega
  have rootCard : 2 < (Laurent.rootCoset 3 1).card := by rw [Laurent.card_rootCoset];norm_num
  obtain ⟨s,hs,t,ht,u,hu,dst,dsu,dtu⟩ := Finset.two_lt_card.mp rootCard
  let lam := (t-u)/(t-s)
  let mu := (u-s)/(t-s)
  have hlam : lam ≠ 0 := div_ne_zero (sub_ne_zero.mpr dtu) (sub_ne_zero.mpr dst.symm)
  have hmu : mu ≠ 0 := div_ne_zero (sub_ne_zero.mpr dsu.symm) (sub_ne_zero.mpr dst.symm)
  apply triangle_impossible (pencil U V s) (pencil U V t) (pencil U V u)
    (independent_root_supports U V independent samples s (root_of_mem hs))
    (independent_root_supports U V independent samples t (root_of_mem ht))
    (independent_root_supports U V independent samples u (root_of_mem hu))
    lam mu hlam hmu (combination U V s t u dst)
  rw [←union_eq_two_samples U V s t dst]
  exact unionSix

/-- The fixed four-word support is a conclusion, including m=3. No residual
matching, selected safe factorization, or desired ruling is supplied. -/
theorem independent_union_le_four {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (independent : ¬ Dependent U V)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    (unionSupport U V).card ≤ 4 := by
  by_cases hm3 : m=3
  · subst m
    exact three_roots_union_le_four U V independent samples
  · exact four_roots_union_le_four (by omega) U V independent samples

theorem independent_support_exact {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (independent : ¬ Dependent U V)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t))
    (t : ℂ) (ht : t^m=1) : support (pencil U V t)=unionSupport U V := by
  classical
  obtain ⟨D⟩ := independent_root_supports U V independent samples t ht
  apply Finset.eq_of_subset_of_card_le
  · exact ClosureRootPencilCount.pencilSupport_subset_union U V t
  · rw [D.support_card]
    exact independent_union_le_four hm U V independent samples

theorem independent_samples_common_support {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (independent : ¬ Dependent U V)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t))
    (s t : ℂ) (hs : s^m=1) (ht : t^m=1) :
    support (pencil U V s)=support (pencil U V t) :=
  (independent_support_exact hm U V independent samples s hs).trans
    (independent_support_exact hm U V independent samples t ht).symm

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
