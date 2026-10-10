import Holant.ReedMuller.TwoChart.GeometryBasic

/-! Parity for alternating binary spaces, and planes through prescribed vectors. -/
namespace Holant.ReedMuller.TwoChart.Geometry
open Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [AddCommGroup V] [Module F₂ V] [FiniteDimensional F₂ V]

theorem even_finrank_of_alternating (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate) (ha : ∀ x, B x x = 0) :
    Even (finrank F₂ V) := by
  generalize hd : finrank F₂ V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz]
    have hp : 0 < finrank F₂ V := by omega
    obtain ⟨x, hx⟩ := finrank_pos_iff_exists_ne_zero.mp hp
    obtain ⟨y, hxy⟩ := exists_pairing_one B hn hx
    let p : IsotropicPair B := ⟨x, y, ha x, hxy, (hB.eq y x).trans hxy⟩
    let P := B.orthogonal p.space
    have hdim : 2 + finrank F₂ P = n := by
      simpa [P, p.finrank_space, hd] using finrank_add_orthogonal B hn p.space
    have he : Even (finrank F₂ P) := ih (finrank F₂ P) (by omega)
      (B.restrict P) (hB.restrict P)
      (orthogonal_nondegenerate B hB hn p.space (p.nondegenerate hB))
      (fun z => ha z) rfl
    obtain ⟨k, hk⟩ := he
    exact ⟨k + 1, by omega⟩

theorem exists_anisotropic_of_odd (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate) (hd : Odd (finrank F₂ V)) :
    ∃ x : V, B x x = 1 := by
  by_contra! h
  have ha : ∀ x, B x x = 0 := fun x =>
    (scalar_eq_zero_or_one (B x x)).resolve_right (h x)
  exact (Nat.not_even_iff_odd.mpr hd) (even_finrank_of_alternating B hB hn ha)

/-- Every vector in an even nondegenerate symmetric binary space lies in an
even nondegenerate subspace of dimension at most two. Alternating planes are
allowed, which is essential for the character-aware localization. -/
theorem exists_small_even_envelope (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate) (hd : Even (finrank F₂ V)) (x : V) :
    ∃ U : Submodule F₂ V, x ∈ U ∧ (B.restrict U).Nondegenerate ∧
      Even (finrank F₂ U) ∧ finrank F₂ U ≤ 2 := by
  by_cases hx : x = 0
  · refine ⟨⊥, by simp [hx], ?_, by simp, by simp⟩
    exact ⟨fun z _ => Subsingleton.elim _ _, fun z _ => Subsingleton.elim _ _⟩
  by_cases hxx : B x x = 0
  · obtain ⟨y, hxy⟩ := exists_pairing_one B hn hx
    let p : IsotropicPair B := ⟨x, y, hxx, hxy, (hB.eq y x).trans hxy⟩
    exact ⟨p.space, p.x_mem, p.nondegenerate hB, by rw [p.finrank_space]; decide,
      by rw [p.finrank_space]⟩
  · let L : Submodule F₂ V := Submodule.span F₂ {x}
    let P := B.orthogonal L
    have hL : finrank F₂ L = 1 := finrank_span_singleton hx
    have hnP : (B.restrict P).Nondegenerate :=
      B.restrict_nondegenerate_orthogonal_spanSingleton hn hB.isRefl hxx
    have hdim : 1 + finrank F₂ P = finrank F₂ V := by
      simpa only [← hL] using finrank_add_orthogonal B hn L
    have ho : Odd (finrank F₂ P) := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 1, by omega⟩
    obtain ⟨y, hyy⟩ := exists_anisotropic_of_odd (B.restrict P) (hB.restrict P) hnP ho
    have hxy : B x y = 0 := y.property x (Submodule.subset_span (by simp))
    have hyx : B (y : V) x = 0 := (hB.eq y x).trans hxy
    have hxx' : B x x = 1 := scalar_eq_one_of_ne_zero hxx
    let p : IsotropicPair B :=
      { x := x + y
        y := x
        xx := by
          change B (y : V) (y : V) = 1 at hyy
          simp [hxx', hxy, hyx, hyy, vector_add_self]
        xy := by simp [hxx', hyx]
        yx := by simp [hxx', hxy] }
    exact ⟨p.space, p.y_mem, p.nondegenerate hB, by rw [p.finrank_space]; decide,
      by rw [p.finrank_space]⟩

end
end Holant.ReedMuller.TwoChart.Geometry
