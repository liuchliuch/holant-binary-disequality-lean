import Holant.Platonic.RainbowLocalization.PresentationLine
import Holant.Certificates.RainbowOrbit.Proportional

/-! A rainbow line contains exactly three nonsingular matching-product points. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization
open Holant Holant.Pauli.ExoticKlein MatchingCut
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.RainbowOrbit (Proportional)
variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The third matching on a rainbow line is uniquely determined by the
first two, pointwise on the original physical ports. -/
theorem third_matching_unique {r₀ r₁ r₂ r₃ : ℕ}
    (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂) (M₃ : Matching P r₃)
    (h₂ : CutRankTriangle M₀ M₁ M₂) (h₁ : CutRankTriangle M₀ M₂ M₁)
    (h₀ : CutRankTriangle M₁ M₂ M₀)
    (h₃ : CutRankTriangle M₀ M₁ M₃) (h₁' : CutRankTriangle M₀ M₃ M₁)
    (h₀' : CutRankTriangle M₁ M₃ M₀) : M₂.mate = M₃.mate := by
  ext p
  by_cases he : M₀.mate p = M₁.mate p
  · have ha := edge_of_two M₀ M₁ M₂ h₂ p (M₀.mate p) rfl he.symm
    have hb := edge_of_two M₀ M₁ M₃ h₃ p (M₀.mate p) rfl he.symm
    exact ha.trans hb.symm
  · have ha := (local_four_port_relations M₀ M₁ M₂ h₂ h₁ h₀ p he).2.2.2.1
    have hb := (local_four_port_relations M₀ M₁ M₃ h₃ h₁' h₀' p he).2.2.2.1
    exact ha.symm.trans hb

/-- A rainbow line has at most one projective point with a specified one
of its matching types.  Repeated-matching exclusion is a rank argument. -/
theorem same_matching_on_line_proportional (D E F : Presentation ℂ P)
    (hD : ∀ e, (D.matrix e).det ≠ 0) (hE : ∀ e, (E.matrix e).det ≠ 0)
    (hF : ∀ e, (F.matrix e).det ≠ 0)
    (hcD : D.scalar ≠ 0) (hcE : E.scalar ≠ 0) (hcF : F.scalar ≠ 0)
    (hme : (presentationMatching D).mate = (presentationMatching E).mate)
    (hEF : (presentationMatching E).mate ≠ (presentationMatching F).mate)
    (hline : D.tensor ∈ Submodule.span ℂ ({E.tensor,F.tensor} : Set (Tensor ℂ P))) :
    Proportional D.tensor E.tensor := by
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hline
  have hb : b = 0 := by
    by_contra hb
    have hsol : F.tensor = (-b⁻¹*a) • E.tensor + b⁻¹ • D.tensor := by
      rw [← he]
      ext x
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      field_simp
      ring
    have ht := presentation_cut_triangle E D F hE hD hF hcE hcD hcF _ _ hsol
    apply hEF
    apply Equiv.ext
    intro p
    exact (edge_of_two (presentationMatching E) (presentationMatching D)
      (presentationMatching F) ht p ((presentationMatching E).mate p) rfl
      (by rw [hme])).symm
  have hd : D.tensor = a • E.tensor := by simpa [hb] using he.symm
  refine ⟨a,?_,hd⟩
  intro ha
  have hz : D.tensor = 0 := by simpa [ha] using hd
  exact productValue_nonzero D.ports D.matrix D.scalar hD hcD hz

/-- The exact three-point upper bound, with the candidate fourth point
given by a literal nonsingular matching presentation on the original ports. -/
theorem matching_point_on_rainbow_line (D₀ D₁ D₂ D : Presentation ℂ P)
    (h₀ : ∀ e, (D₀.matrix e).det ≠ 0) (h₁ : ∀ e, (D₁.matrix e).det ≠ 0)
    (h₂ : ∀ e, (D₂.matrix e).det ≠ 0) (hD : ∀ e, (D.matrix e).det ≠ 0)
    (hc₀ : D₀.scalar ≠ 0) (hc₁ : D₁.scalar ≠ 0) (hc₂ : D₂.scalar ≠ 0) (hcD : D.scalar ≠ 0)
    (hne₀₁ : (presentationMatching D₀).mate ≠ (presentationMatching D₁).mate)
    (hne₂₀ : (presentationMatching D₂).mate ≠ (presentationMatching D₀).mate)
    (hne₂₁ : (presentationMatching D₂).mate ≠ (presentationMatching D₁).mate)
    (hline₂ : D₂.tensor ∈ Submodule.span ℂ ({D₀.tensor,D₁.tensor} : Set (Tensor ℂ P)))
    (hlineD : D.tensor ∈ Submodule.span ℂ ({D₀.tensor,D₁.tensor} : Set (Tensor ℂ P))) :
    Proportional D.tensor D₀.tensor ∨ Proportional D.tensor D₁.tensor ∨ Proportional D.tensor D₂.tensor := by
  by_cases hm₀ : (presentationMatching D).mate = (presentationMatching D₀).mate
  · exact Or.inl (same_matching_on_line_proportional D D₀ D₁ hD h₀ h₁ hcD hc₀ hc₁ hm₀ hne₀₁ hlineD)
  by_cases hm₁ : (presentationMatching D).mate = (presentationMatching D₁).mate
  · right; left
    apply same_matching_on_line_proportional D D₁ D₀ hD h₁ h₀ hcD hc₁ hc₀ hm₁ hne₀₁.symm
    simpa only [Set.pair_comm D₁.tensor D₀.tensor] using hlineD
  have ht₂ := presentation_three_cut_triangles D₀ D₁ D₂ h₀ h₁ h₂ hc₀ hc₁ hc₂ hne₂₀ hne₂₁ hline₂
  have htD := presentation_three_cut_triangles D₀ D₁ D h₀ h₁ hD hc₀ hc₁ hcD hm₀ hm₁ hlineD
  have hm₂ : (presentationMatching D).mate = (presentationMatching D₂).mate :=
    (third_matching_unique _ _ _ _ ht₂.1 ht₂.2.1 ht₂.2.2 htD.1 htD.2.1 htD.2.2).symm
  obtain ⟨a,b,ha,hb,he⟩ := nonzero_line_coefficients D₀ D₁ D₂ h₀ h₁ h₂ hc₀ hc₁ hc₂ hne₂₀ hne₂₁ hline₂
  obtain ⟨x,y,hxy⟩ := Submodule.mem_span_pair.mp hlineD
  have hlineD' : D.tensor ∈ Submodule.span ℂ ({D₂.tensor,D₀.tensor} : Set (Tensor ℂ P)) := by
    apply Submodule.mem_span_pair.mpr
    refine ⟨y*b⁻¹,x-y*b⁻¹*a,?_⟩
    rw [he,←hxy]
    ext t
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    field_simp
    ring
  exact Or.inr (Or.inr (same_matching_on_line_proportional D D₂ D₀ hD h₂ h₀
    hcD hc₂ hc₀ hm₂ hne₂₀ hlineD'))

end Holant.Platonic.RainbowLocalization
