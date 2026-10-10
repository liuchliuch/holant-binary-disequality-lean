import Holant.ReedMuller.TwoChart.GeometryParity
import Holant.ReedMuller.TwoChart.GeometrySum

/-! Bounded nondegenerate envelopes in an even binary symmetric space. -/
namespace Holant.ReedMuller.TwoChart.Geometry
open Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [AddCommGroup V] [Module F₂ V] [FiniteDimensional F₂ V]

/-- Adjoining one prescribed vector costs at most one nondegenerate plane. -/
theorem exists_even_extension (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate) (hd : Even (finrank F₂ V))
    (U : Submodule F₂ V) (hU : (B.restrict U).Nondegenerate)
    (heU : Even (finrank F₂ U)) (x : V) :
    ∃ U' : Submodule F₂ V, U ≤ U' ∧ x ∈ U' ∧ (B.restrict U').Nondegenerate ∧
      Even (finrank F₂ U') ∧ finrank F₂ U' ≤ finrank F₂ U + 2 := by
  let P := B.orthogonal U
  have hUP := B.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hU
  have hnP := orthogonal_nondegenerate B hB hn U hU
  have hdim := finrank_add_orthogonal B hn U
  have heP : Even (finrank F₂ P) := by
    obtain ⟨k, hk⟩ := hd
    obtain ⟨l, hl⟩ := heU
    exact ⟨k - l, by dsimp [P]; omega⟩
  have hx : x ∈ U ⊔ B.orthogonal U := by rw [hUP.sup_eq_top]; trivial
  obtain ⟨u, hu, p, hp, hxp⟩ := Submodule.mem_sup.mp hx
  obtain ⟨Q, hpQ, hnQ, heQ, hdQ⟩ := exists_small_even_envelope
    (B.restrict P) (hB.restrict P) hnP heP (⟨p, hp⟩ : P)
  let Q' := Q.map P.subtype
  have hQP : Q' ≤ B.orthogonal U := map_subtype_le P Q
  have hnQ' : (B.restrict Q').Nondegenerate := nondegenerate_map_subtype B P Q hnQ
  have hdim' : finrank F₂ ↥(U ⊔ Q') = finrank F₂ U + finrank F₂ Q := by
    rw [finrank_sup_of_disjoint U Q' (disjoint_of_le_orthogonal B hB U Q' hU hQP)]
    rw [Submodule.finrank_map_subtype_eq]
  refine ⟨U ⊔ Q', le_sup_left, ?_, nondegenerate_sup B hB U Q' hU hnQ' hQP, ?_, ?_⟩
  · rw [← hxp]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hu)
      (Submodule.mem_sup_right (Submodule.mem_map.mpr ⟨⟨p, hp⟩, hpQ, rfl⟩))
  · rw [hdim']
    exact heU.add heQ
  · rw [hdim']
    omega

/-- The equal-direction character-aware case: the shift and the character
difference fit into an even nondegenerate space of dimension at most four. -/
theorem exists_even_envelope_two (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate) (hd : Even (finrank F₂ V))
    (Δ ρ : V) :
    ∃ U : Submodule F₂ V, Δ ∈ U ∧ ρ ∈ U ∧ (B.restrict U).Nondegenerate ∧
      Even (finrank F₂ U) ∧ finrank F₂ U ≤ 4 := by
  obtain ⟨U, hΔ, hnU, heU, hdU⟩ := exists_small_even_envelope B hB hn hd Δ
  obtain ⟨U', hle, hρ, hnU', heU', hdU'⟩ := exists_even_extension B hB hn hd U hnU heU ρ
  exact ⟨U', hle hΔ, hρ, hnU', heU', by omega⟩

/-- The different-direction case: preserve the separating nondegenerate
plane and both shift/character differences in dimension at most six. -/
theorem exists_even_envelope_separating_pair (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate) (hd : Even (finrank F₂ V))
    (s t Δ ρ : V) (hs : B s s = 0) (hst : B s t = 1) :
    ∃ U : Submodule F₂ V, s ∈ U ∧ t ∈ U ∧ Δ ∈ U ∧ ρ ∈ U ∧
      (B.restrict U).Nondegenerate ∧ Even (finrank F₂ U) ∧ finrank F₂ U ≤ 6 := by
  let p : IsotropicPair B := ⟨s, t, hs, hst, (hB.eq t s).trans hst⟩
  have he : Even (finrank F₂ p.space) := by rw [p.finrank_space]; decide
  obtain ⟨U, hle, hΔ, hnU, heU, hdU⟩ :=
    exists_even_extension B hB hn hd p.space (p.nondegenerate hB) he Δ
  obtain ⟨U', hle', hρ, hnU', heU', hdU'⟩ :=
    exists_even_extension B hB hn hd U hnU heU ρ
  refine ⟨U', hle' (hle p.x_mem), hle' (hle p.y_mem), hle' hΔ, hρ, hnU', heU', ?_⟩
  rw [p.finrank_space] at hdU
  omega

end
end Holant.ReedMuller.TwoChart.Geometry
