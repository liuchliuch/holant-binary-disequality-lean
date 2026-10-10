import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineCycleContractionFamily

/-! Exact coordinate projections of nonzero cycle contractions. A singleton
cycle fixes its label; every coordinate of a longer cycle attains all labels. -/

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open scoped BigOperators

/-- Nonvanishing of the literal Boolean contraction is exactly the affine
label equation obtained from the actual matrix trace. -/
theorem cycleContraction_ne_zero_iff (length : ℕ) (hLength : 0 < length)
    (fixed : Fin length → Label) (mReverse nReverse : Fin length → Bool)
    (labels : Fin length → Label) :
    cycleContraction length fixed mReverse nReverse labels ≠ 0 ↔
      (∑ i, dualLabelMap (mReverse i) (labels i)) =
        ∑ i, directLabelMap (nReverse i) (fixed i) := by
  cases length with
  | zero => exact (Nat.not_lt_zero _ hLength).elim
  | succ n =>
    rw [cycleContraction_succ]
    exact cycleCoefficient_ne_zero_iff n fixed mReverse nReverse labels

private theorem affine_coordinate_surjective {I : Type*} [Fintype I] [DecidableEq I]
    [Nontrivial I] (maps : I → Label ≃+ Label) (target : Label) (i : I) (a : Label) :
    ∃ labels : I → Label, (∑ k, maps k (labels k)) = target ∧ labels i = a := by
  obtain ⟨j, hji⟩ := exists_ne i
  let b := (maps j).symm (target - maps i a)
  let labels : I → Label := fun k => if k = i then a else if k = j then b else 0
  refine ⟨labels, ?_, by simp [labels]⟩
  have hterm (k : I) : maps k (labels k) =
      (if k = i then maps i a else 0) + (if k = j then maps j b else 0) := by
    by_cases hki : k = i
    · subst k
      simp only [labels, ite_eq_left rfl, ite_eq_right (Ne.symm hji), ite_true, add_zero]
    · by_cases hkj : k = j
      · subst k
        simp only [labels, ite_eq_right hji, ite_true, zero_add]
      · simp only [labels, ite_eq_right hki, ite_eq_right hkj, map_zero, zero_add]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, b, AddEquiv.apply_symm_apply]
  abel

/-- Fixing any coordinate to any of the four labels leaves a nonzero
coefficient whenever the cycle contains at least two M-edges. -/
theorem cycleContraction_coordinate_surjective (length : ℕ) (hLength : 2 ≤ length)
    (fixed : Fin length → Label) (mReverse nReverse : Fin length → Bool)
    (i : Fin length) (a : Label) :
    ∃ labels : Fin length → Label,
      cycleContraction length fixed mReverse nReverse labels ≠ 0 ∧ labels i = a := by
  let : Nontrivial (Fin length) := Fin.nontrivial_iff_two_le.mpr hLength
  obtain ⟨labels, hs, hi⟩ := affine_coordinate_surjective
    (fun i => dualLabelMap (mReverse i))
    (∑ i, directLabelMap (nReverse i) (fixed i)) i a
  exact ⟨labels, (cycleContraction_ne_zero_iff length (by omega)
    fixed mReverse nReverse labels).mpr hs, hi⟩

/-- A common-edge cycle has one fixed original M-label throughout its
nonzero support, for every choice of traversal orientations. -/
theorem cycleContraction_coordinate_fixed (length : ℕ) (hLength : length = 1)
    (fixed : Fin length → Label) (mReverse nReverse : Fin length → Bool)
    (labels labels' : Fin length → Label)
    (h : cycleContraction length fixed mReverse nReverse labels ≠ 0)
    (h' : cycleContraction length fixed mReverse nReverse labels' ≠ 0)
    (i : Fin length) : labels i = labels' i := by
  subst length
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  apply (dualLabelMap (mReverse 0)).injective
  have hs := (cycleContraction_ne_zero_iff 1 (by decide) fixed mReverse nReverse labels).mp h
  have hs' := (cycleContraction_ne_zero_iff 1 (by decide) fixed mReverse nReverse labels').mp h'
  simp only [Fin.sum_univ_one] at hs hs'
  exact hs.trans hs'.symm

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- A family of positive cycles always has at least one nonzero original
label assignment, including the empty family. -/
theorem cycleFamilyContraction_exists (length : C → ℕ) (hLength : ∀ c, 0 < length c)
    (fixed : (Σ c, Fin (length c)) → Label)
    (mReverse nReverse : (Σ c, Fin (length c)) → Bool) :
    ∃ labels, cycleFamilyContraction length fixed mReverse nReverse labels ≠ 0 := by
  have hp : 0 < Fintype.card {labels : (Σ c, Fin (length c)) → Label //
      cycleFamilyContraction length fixed mReverse nReverse labels ≠ 0} := by
    rw [cycleFamilyContraction_support_card length hLength]
    exact pow_pos (by decide) _
  obtain ⟨labels⟩ := Fintype.card_pos_iff.mp hp
  exact ⟨labels.val, labels.property⟩

/-- Every coordinate on a nonsingleton cycle attains all four labels in
the support of the actual global contraction. -/
theorem cycleFamilyContraction_coordinate_surjective
    (length : C → ℕ) (hLength : ∀ c, 0 < length c)
    (fixed : (Σ c, Fin (length c)) → Label)
    (mReverse nReverse : (Σ c, Fin (length c)) → Bool)
    (e : Σ c, Fin (length c)) (he : 2 ≤ length e.1) (a : Label) :
    ∃ labels : (Σ c, Fin (length c)) → Label,
      cycleFamilyContraction length fixed mReverse nReverse labels ≠ 0 ∧ labels e = a := by
  classical
  obtain ⟨base, hbase⟩ := cycleFamilyContraction_exists length hLength fixed mReverse nReverse
  obtain ⟨localLabels, hlocal, ha⟩ := cycleContraction_coordinate_surjective (length e.1) he
    (fun i => fixed ⟨e.1, i⟩) (fun i => mReverse ⟨e.1, i⟩)
    (fun i => nReverse ⟨e.1, i⟩) e.2 a
  let supports := cycleFamilyContractionSupportEquiv length fixed mReverse nReverse ⟨base, hbase⟩
  let replacement := Function.update supports e.1 ⟨localLabels, hlocal⟩
  let result := (cycleFamilyContractionSupportEquiv length fixed mReverse nReverse).symm replacement
  refine ⟨result.val, result.property, ?_⟩
  change (Function.update supports e.1 ⟨localLabels, hlocal⟩ e.1).val e.2 = a
  rw [Function.update_self]
  exact ha

/-- Every coordinate on a singleton cycle is fixed across the nonzero
support of the actual global contraction. -/
theorem cycleFamilyContraction_coordinate_fixed
    (length : C → ℕ)
    (fixed : (Σ c, Fin (length c)) → Label)
    (mReverse nReverse : (Σ c, Fin (length c)) → Bool)
    (labels labels' : (Σ c, Fin (length c)) → Label)
    (h : cycleFamilyContraction length fixed mReverse nReverse labels ≠ 0)
    (h' : cycleFamilyContraction length fixed mReverse nReverse labels' ≠ 0)
    (e : Σ c, Fin (length c)) (he : length e.1 = 1) : labels e = labels' e := by
  rw [cycleFamilyContraction_eq_prod] at h h'
  exact cycleContraction_coordinate_fixed (length e.1) he
    (fun i => fixed ⟨e.1, i⟩) (fun i => mReverse ⟨e.1, i⟩)
    (fun i => nReverse ⟨e.1, i⟩) (fun i => labels ⟨e.1, i⟩)
    (fun i => labels' ⟨e.1, i⟩)
    ((Finset.prod_ne_zero_iff.mp h) e.1 (Finset.mem_univ _))
    ((Finset.prod_ne_zero_iff.mp h') e.1 (Finset.mem_univ _)) e.2

/-- An original edge label varies on the nonzero support if and only if
its cycle contains at least two edges. -/
theorem cycleFamilyContraction_coordinate_varies_iff
    (length : C → ℕ) (hLength : ∀ c, 0 < length c)
    (fixed : (Σ c, Fin (length c)) → Label)
    (mReverse nReverse : (Σ c, Fin (length c)) → Bool)
    (e : Σ c, Fin (length c)) :
    (∃ labels labels' : (Σ c, Fin (length c)) → Label,
      cycleFamilyContraction length fixed mReverse nReverse labels ≠ 0 ∧
      cycleFamilyContraction length fixed mReverse nReverse labels' ≠ 0 ∧
      labels e ≠ labels' e) ↔ 2 ≤ length e.1 := by
  constructor
  · rintro ⟨labels, labels', h, h', hne⟩
    by_contra hn
    have he : length e.1 = 1 := by have := hLength e.1; omega
    exact hne (cycleFamilyContraction_coordinate_fixed length fixed mReverse nReverse
      labels labels' h h' e he)
  · intro he
    obtain ⟨labels, h, hzero⟩ := cycleFamilyContraction_coordinate_surjective
      length hLength fixed mReverse nReverse e he 0
    obtain ⟨labels', h', hx⟩ := cycleFamilyContraction_coordinate_surjective
      length hLength fixed mReverse nReverse e he xLabel
    refine ⟨labels, labels', h, h', ?_⟩
    rw [hzero, hx]
    exact zero_ne_x

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
