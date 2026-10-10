import Holant.ReedMuller.TwoChart.GeometrySum

/-! Every even nondegenerate binary symmetric space has a Lagrangian.
This includes alternating spaces. -/
namespace Holant.ReedMuller.TwoChart.Geometry
open Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [AddCommGroup V] [Module F₂ V] [FiniteDimensional F₂ V]

theorem exists_halfDimension_selfOrthogonal (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate) (hd : Even (finrank F₂ V)) :
    ∃ J : Submodule F₂ V, SelfOrthogonal B J ∧ 2 * finrank F₂ J = finrank F₂ V := by
  generalize heq : finrank F₂ V = n at *
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hz : n = 0
    · refine ⟨⊥, ?_, by simp [hz]⟩
      intro x hx y hy
      simp only [Submodule.mem_bot] at hx
      simp [hx]
    have htwo : 2 ≤ finrank F₂ V := by
      obtain ⟨k, hk⟩ := hd
      omega
    obtain ⟨p⟩ := exists_isotropicPair B hB hn htwo
    let P := B.orthogonal p.space
    have hdim : 2 + finrank F₂ P = n := by
      simpa [P, p.finrank_space, heq] using finrank_add_orthogonal B hn p.space
    have heP : Even (finrank F₂ P) := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 1, by omega⟩
    obtain ⟨K, hK, hdK⟩ := ih (finrank F₂ P) (by omega)
      (B.restrict P) (hB.restrict P)
      (orthogonal_nondegenerate B hB hn p.space (p.nondegenerate hB)) rfl heP
    let L : Submodule F₂ V := Submodule.span F₂ {p.x}
    let K' := K.map P.subtype
    have hL : L ≤ p.space := Submodule.span_le.mpr (by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      simpa [hx] using p.x_mem)
    have hK' : K' ≤ P := map_subtype_le P K
    have hdis : Disjoint L K' :=
      ((B.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl
        (p.nondegenerate hB)).disjoint.mono_left hL).mono_right hK'
    have hcross : K' ≤ B.orthogonal L :=
      le_trans hK' (B.orthogonal_le hL)
    have hdL : finrank F₂ L = 1 := finrank_span_singleton p.x_ne_zero
    refine ⟨L ⊔ K', selfOrthogonal_sup B hB L K'
      (selfOrthogonal_span_singleton B p.xx)
      (selfOrthogonal_map_subtype B P K hK) hcross, ?_⟩
    rw [finrank_sup_of_disjoint L K' hdis, hdL, Submodule.finrank_map_subtype_eq]
    omega

/-- The actual subspace equals its ambient-relative orthogonal complement. -/
theorem exists_selfDual (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate) (hd : Even (finrank F₂ V)) :
    ∃ J : Submodule F₂ V, J = B.orthogonal J ∧
      SelfOrthogonal B J ∧ 2 * finrank F₂ J = finrank F₂ V := by
  obtain ⟨J, hJ, hdJ⟩ := exists_halfDimension_selfOrthogonal B hB hn hd
  exact ⟨J, selfDual_of_selfOrthogonal_halfDimension B hn J hJ hdJ, hJ, hdJ⟩

end
end Holant.ReedMuller.TwoChart.Geometry
