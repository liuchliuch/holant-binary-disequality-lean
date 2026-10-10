import Holant.Platonic.RainbowLocalization.LineRanks
import Holant.Platonic.RainbowLocalization.LocalFourPorts
import Holant.Certificates.MatchingContractionClosure.Presentation

/-! The rank constraints come from actual matching presentations on one line. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization
open Holant Holant.Pauli.ExoticKlein MatchingCut
open Holant.Certificates.MatchingContractionClosure
variable {P : Type*} [Fintype P] [DecidableEq P]

def presentationMatching (D : Presentation ℂ P) : Matching P D.edges := ⟨D.ports⟩

theorem presentation_rank (D : Presentation ℂ P) (s : P → Bool)
    (hD : ∀ e, (D.matrix e).det ≠ 0) (hc : D.scalar ≠ 0) :
    (flatten s D.tensor).rank = 2 ^ Fintype.card (Crossing (presentationMatching D) s) :=
  flatten_product_rank (presentationMatching D) s D.matrix D.scalar hD hc

/-- A proportionality of nonsingular matching products forces equality of
their underlying perfect matchings, irrespective of endpoint orientations. -/
theorem matching_eq_of_tensor_smul (D E : Presentation ℂ P)
    (hD : ∀ e, (D.matrix e).det ≠ 0) (hE : ∀ e, (E.matrix e).det ≠ 0)
    (hcD : D.scalar ≠ 0) (hcE : E.scalar ≠ 0)
    (c : ℂ) (he : D.tensor = c • E.tensor) :
    (presentationMatching D).mate = (presentationMatching E).mate := by
  have hcn : c ≠ 0 := by
    intro hc
    have hz : D.tensor = 0 := by simpa [hc] using he
    exact productValue_nonzero D.ports D.matrix D.scalar hD hcD hz
  ext p
  let q := (presentationMatching D).mate p
  have hpq : p ≠ q := (Matching.mate_ne_self (presentationMatching D) p).symm
  by_contra h
  have hn : (presentationMatching E).mate p ≠ q := Ne.symm h
  have h₀ := presentation_rank D (cut {p,q}) hD hcD
  have h₁ := presentation_rank E (cut {p,q}) hE hcE
  rw [crossing_pair_of_matched (presentationMatching D) p q hpq rfl] at h₀
  rw [crossing_pair_of_unmatched (presentationMatching E) p q hpq hn] at h₁
  have hh : (flatten (cut {p,q}) D.tensor).rank = (flatten (cut {p,q}) E.tensor).rank := by
    rw [he,flatten_smul,Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero hcn)]
  rw [h₀,h₁] at hh
  norm_num at hh

/-- Distinct actual matchings on one projective line have both line
coefficients nonzero.  Nontrivial coefficients are derived, not assumed. -/
theorem nonzero_line_coefficients (D₀ D₁ D₂ : Presentation ℂ P)
    (h₀ : ∀ e, (D₀.matrix e).det ≠ 0) (h₁ : ∀ e, (D₁.matrix e).det ≠ 0)
    (h₂ : ∀ e, (D₂.matrix e).det ≠ 0)
    (hc₀ : D₀.scalar ≠ 0) (hc₁ : D₁.scalar ≠ 0) (hc₂ : D₂.scalar ≠ 0)
    (hne₂₀ : (presentationMatching D₂).mate ≠ (presentationMatching D₀).mate)
    (hne₂₁ : (presentationMatching D₂).mate ≠ (presentationMatching D₁).mate)
    (hline : D₂.tensor ∈ Submodule.span ℂ ({D₀.tensor,D₁.tensor} : Set (Tensor ℂ P))) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ D₂.tensor = a • D₀.tensor + b • D₁.tensor := by
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hline
  refine ⟨a,b,?_,?_,he.symm⟩
  · intro ha
    apply hne₂₁
    apply matching_eq_of_tensor_smul D₂ D₁ h₂ h₁ hc₂ hc₁ b
    simpa [ha] using he.symm
  · intro hb
    apply hne₂₀
    apply matching_eq_of_tensor_smul D₂ D₀ h₂ h₀ hc₂ hc₀ a
    simpa [hb] using he.symm

theorem presentation_cut_triangle (D₀ D₁ D₂ : Presentation ℂ P)
    (h₀ : ∀ e, (D₀.matrix e).det ≠ 0) (h₁ : ∀ e, (D₁.matrix e).det ≠ 0)
    (h₂ : ∀ e, (D₂.matrix e).det ≠ 0)
    (hc₀ : D₀.scalar ≠ 0) (hc₁ : D₁.scalar ≠ 0) (hc₂ : D₂.scalar ≠ 0)
    (a b : ℂ) (he : D₂.tensor = a • D₀.tensor + b • D₁.tensor) :
    CutRankTriangle (presentationMatching D₀) (presentationMatching D₁) (presentationMatching D₂) := by
  intro S
  exact crossing_pow_le_of_line (presentationMatching D₀) (presentationMatching D₁)
    (presentationMatching D₂) D₀.matrix D₁.matrix D₂.matrix
    D₀.scalar D₁.scalar D₂.scalar a b h₀ h₁ h₂ hc₀ hc₁ hc₂ he (cut S)

/-- Every permutation of the cut rank triangle follows from the original
literal line membership and distinctness of the given matchings. -/
theorem presentation_three_cut_triangles (D₀ D₁ D₂ : Presentation ℂ P)
    (h₀ : ∀ e, (D₀.matrix e).det ≠ 0) (h₁ : ∀ e, (D₁.matrix e).det ≠ 0)
    (h₂ : ∀ e, (D₂.matrix e).det ≠ 0)
    (hc₀ : D₀.scalar ≠ 0) (hc₁ : D₁.scalar ≠ 0) (hc₂ : D₂.scalar ≠ 0)
    (hne₂₀ : (presentationMatching D₂).mate ≠ (presentationMatching D₀).mate)
    (hne₂₁ : (presentationMatching D₂).mate ≠ (presentationMatching D₁).mate)
    (hline : D₂.tensor ∈ Submodule.span ℂ ({D₀.tensor,D₁.tensor} : Set (Tensor ℂ P))) :
    CutRankTriangle (presentationMatching D₀) (presentationMatching D₁) (presentationMatching D₂) ∧
    CutRankTriangle (presentationMatching D₀) (presentationMatching D₂) (presentationMatching D₁) ∧
    CutRankTriangle (presentationMatching D₁) (presentationMatching D₂) (presentationMatching D₀) := by
  obtain ⟨a,b,ha,hb,he⟩ := nonzero_line_coefficients D₀ D₁ D₂ h₀ h₁ h₂ hc₀ hc₁ hc₂ hne₂₀ hne₂₁ hline
  have he₀ : D₀.tensor = (-a⁻¹*b) • D₁.tensor + a⁻¹ • D₂.tensor := by
    rw [he]
    ext x
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    field_simp
    ring
  have he₁ : D₁.tensor = (-b⁻¹*a) • D₀.tensor + b⁻¹ • D₂.tensor := by
    rw [he]
    ext x
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    field_simp
    ring
  exact ⟨presentation_cut_triangle D₀ D₁ D₂ h₀ h₁ h₂ hc₀ hc₁ hc₂ a b he,
    presentation_cut_triangle D₀ D₂ D₁ h₀ h₂ h₁ hc₀ hc₂ hc₁ _ _ he₁,
    presentation_cut_triangle D₁ D₂ D₀ h₁ h₂ h₀ hc₁ hc₂ hc₀ _ _ he₀⟩

end Holant.Platonic.RainbowLocalization
