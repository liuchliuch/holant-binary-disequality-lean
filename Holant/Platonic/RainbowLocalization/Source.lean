import Holant.Platonic.RainbowLocalization.AlgebraicLocalization

/-! Source-level algebraic clause of rainbow matching-line localization.
The physical one-vertex realization and the encoded Turing reduction are
separate obligations and are not asserted in this module.
-/
noncomputable section
namespace Holant.Platonic.RainbowLocalization
open Holant Holant.Pauli.ExoticKlein MatchingCut
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.RainbowOrbit (Proportional)
variable {P : Type*} [Fintype P] [DecidableEq P]

theorem AlgebraicLocalization.exceptional_edges {D₀ D₁ D₂ : Presentation ℂ P}
    (L : AlgebraicLocalization D₀ D₁ D₂) :
    L.exceptional₀.edges = 2 ∧ L.exceptional₁.edges = 2 ∧ L.exceptional₂.edges = 2 := by
  have h₀ := (presentationMatching L.exceptional₀).port_card
  have h₁ := (presentationMatching L.exceptional₁).port_card
  have h₂ := (presentationMatching L.exceptional₂).port_card
  rw [side_cut_card,L.card_ports] at h₀ h₁ h₂
  change 4 = 2 * L.exceptional₀.edges at h₀
  change 4 = 2 * L.exceptional₁.edges at h₁
  change 4 = 2 * L.exceptional₂.edges at h₂
  omega

theorem AlgebraicLocalization.common_edges {D₀ D₁ D₂ : Presentation ℂ P}
    (L : AlgebraicLocalization D₀ D₁ D₂) : L.common.edges = (Fintype.card P - 4) / 2 := by
  have h := (presentationMatching L.common).port_card
  rw [side_cut_compl_card,L.card_ports] at h
  change Fintype.card P - 4 = 2 * L.common.edges at h
  omega

/-- This is only the exact closure-kernel count in card-map arities.  It
does not claim that a gadget or a complexity reduction has been built. -/
theorem AlgebraicLocalization.common_edges_for_card_map {D₀ D₁ D₂ : Presentation ℂ P}
    (L : AlgebraicLocalization D₀ D₁ D₂) (n : ℕ) (hP : Fintype.card P = n - 2) :
    L.common.edges = (n - 6) / 2 := by
  rw [L.common_edges,hP]
  congr 1

/-- The whole algebraic source clause: unique four-port localization,
compatible nonzero common matching tensor, exact two-dimensional exceptional
span, and exactly the three specified nonsingular matching-product points. -/
theorem source_rainbow_localization_algebraic (D₀ D₁ D₂ : Presentation ℂ P)
    (h₀ : ∀ e, (D₀.matrix e).det ≠ 0) (h₁ : ∀ e, (D₁.matrix e).det ≠ 0)
    (h₂ : ∀ e, (D₂.matrix e).det ≠ 0)
    (hc₀ : D₀.scalar ≠ 0) (hc₁ : D₁.scalar ≠ 0) (hc₂ : D₂.scalar ≠ 0)
    (hne₀₁ : (presentationMatching D₀).mate ≠ (presentationMatching D₁).mate)
    (hne₂₀ : (presentationMatching D₂).mate ≠ (presentationMatching D₀).mate)
    (hne₂₁ : (presentationMatching D₂).mate ≠ (presentationMatching D₁).mate)
    (hline : D₂.tensor ∈ Submodule.span ℂ ({D₀.tensor,D₁.tensor} : Set (Tensor ℂ P))) :
    Nonempty (AlgebraicLocalization D₀ D₁ D₂) ∧
    ¬ Proportional D₀.tensor D₁.tensor ∧
    ¬ Proportional D₂.tensor D₀.tensor ∧
    ¬ Proportional D₂.tensor D₁.tensor ∧
    ∀ D : Presentation ℂ P, (∀ e, (D.matrix e).det ≠ 0) → D.scalar ≠ 0 →
      (D.tensor ∈ Submodule.span ℂ ({D₀.tensor,D₁.tensor} : Set (Tensor ℂ P)) ↔
        Proportional D.tensor D₀.tensor ∨ Proportional D.tensor D₁.tensor ∨
          Proportional D.tensor D₂.tensor) := by
  refine ⟨algebraic_localization D₀ D₁ D₂ h₀ h₁ h₂ hc₀ hc₁ hc₂ hne₀₁ hne₂₀ hne₂₁ hline,
    ?_,?_,?_,?_⟩
  · rintro ⟨c,hc,he⟩
    exact hne₀₁ (matching_eq_of_tensor_smul D₀ D₁ h₀ h₁ hc₀ hc₁ c he)
  · rintro ⟨c,hc,he⟩
    exact hne₂₀ (matching_eq_of_tensor_smul D₂ D₀ h₂ h₀ hc₂ hc₀ c he)
  · rintro ⟨c,hc,he⟩
    exact hne₂₁ (matching_eq_of_tensor_smul D₂ D₁ h₂ h₁ hc₂ hc₁ c he)
  · intro D hD hcD
    constructor
    · exact matching_point_on_rainbow_line D₀ D₁ D₂ D h₀ h₁ h₂ hD
        hc₀ hc₁ hc₂ hcD hne₀₁ hne₂₀ hne₂₁ hline
    · rintro (⟨c,hc,he⟩ | ⟨c,hc,he⟩ | ⟨c,hc,he⟩) <;> rw [he]
      · exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ c hline

end Holant.Platonic.RainbowLocalization
