import Holant.ReedMuller.TwoChart.GeometryParity
import Holant.ReedMuller.TwoChart.GeometrySum

/-! Splitting anisotropic lines while preserving nonalternation. -/
namespace Holant.ReedMuller.TwoChart.Geometry
open Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [AddCommGroup V] [Module F₂ V] [FiniteDimensional F₂ V]

theorem exists_orthogonal_anisotropic_pair (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate) (hd : 2 ≤ finrank F₂ V)
    (ha : ∃ x, B x x = 1) :
    ∃ x y : V, B x x = 1 ∧ B y y = 1 ∧ B x y = 0 := by
  obtain ⟨x, hx⟩ := ha
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  let L : Submodule F₂ V := Submodule.span F₂ {x}
  let P := B.orthogonal L
  have hnP : (B.restrict P).Nondegenerate :=
    B.restrict_nondegenerate_orthogonal_spanSingleton hn hB.isRefl (by rw [hx]; decide)
  by_cases haP : ∃ y : P, B (y : V) y = 1
  · obtain ⟨y, hy⟩ := haP
    exact ⟨x, y, hx, hy, y.property x (Submodule.subset_span (by simp))⟩
  · have hAlt : ∀ y : P, B (y : V) y = 0 := by
      intro y
      exact (scalar_eq_zero_or_one (B (y : V) y)).resolve_right (fun h => haP ⟨y, h⟩)
    have hdP : 1 + finrank F₂ P = finrank F₂ V := by
      simpa [L, finrank_span_singleton hx0] using finrank_add_orthogonal B hn L
    obtain ⟨u, hu⟩ := (finrank_pos_iff_exists_ne_zero (R := F₂) (M := P)).mp (by omega)
    obtain ⟨v, huv⟩ := exists_pairing_one (B.restrict P) hnP hu
    have hxu : B x (u : V) = 0 := u.property x (Submodule.subset_span (by simp))
    have hxv : B x (v : V) = 0 := v.property x (Submodule.subset_span (by simp))
    have hux : B (u : V) x = 0 := (hB.eq u x).trans hxu
    have hvx : B (v : V) x = 0 := (hB.eq v x).trans hxv
    change B (u : V) (v : V) = 1 at huv
    refine ⟨x + u, x + v, ?_, ?_, ?_⟩
    · simp [hx, hxu, hux, hAlt u]
    · simp [hx, hxv, hvx, hAlt v]
    · simp [hx, hxv, hux, huv, vector_add_self]

/-- A first orthonormal vector can be chosen so the remaining form is either
zero-dimensional or nonalternating again. -/
theorem exists_anisotropic_split (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate) (ha : ∃ x, B x x = 1) :
    ∃ x : V, B x x = 1 ∧
      (finrank F₂ (B.orthogonal (Submodule.span F₂ {x})) = 0 ∨
        ∃ y : B.orthogonal (Submodule.span F₂ {x}), B (y : V) y = 1) := by
  by_cases hd : 2 ≤ finrank F₂ V
  · obtain ⟨x, y, hx, hy, hxy⟩ := exists_orthogonal_anisotropic_pair B hB hn hd ha
    refine ⟨x, hx, Or.inr ⟨⟨y, ?_⟩, hy⟩⟩
    intro z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp [hxy]
  · obtain ⟨x, hx⟩ := ha
    have hx0 : x ≠ 0 := by intro h; simp [h] at hx
    refine ⟨x, hx, Or.inl ?_⟩
    have hdim := finrank_add_orthogonal B hn (Submodule.span F₂ {x})
    rw [finrank_span_singleton hx0] at hdim
    omega

end
end Holant.ReedMuller.TwoChart.Geometry
