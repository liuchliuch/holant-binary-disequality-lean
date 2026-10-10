import Holant.Platonic.RainbowLocalization.UniqueFourPorts
import Holant.Platonic.RainbowLocalization.CutFactors
import Holant.Platonic.RainbowLocalization.ThreePoints
import Holant.Platonic.RainbowLocalization.SpanDimension

/-! Algebraic localization of three actual nonsingular matching products. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization
open Holant Holant.Pauli.ExoticKlein MatchingCut
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.RainbowOrbit (Proportional)
variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The full algebraic output uses genuine matching presentations on the
original four exceptional ports and on their original complement. -/
structure AlgebraicLocalization (D₀ D₁ D₂ : Presentation ℂ P) where
  ports : Finset P
  card_ports : ports.card = 4
  support : ∀ p, p ∈ ports ↔ (presentationMatching D₀).mate p ≠ (presentationMatching D₁).mate p
  inside : ∀ p ∈ ports,
    (presentationMatching D₂).mate p ≠ (presentationMatching D₀).mate p ∧
    (presentationMatching D₂).mate p ≠ (presentationMatching D₁).mate p
  outside : ∀ p, p ∉ ports → (presentationMatching D₀).mate p = (presentationMatching D₁).mate p ∧
    (presentationMatching D₂).mate p = (presentationMatching D₀).mate p
  closed₀ : Closed (presentationMatching D₀) (cut ports)
  closed₁ : Closed (presentationMatching D₁) (cut ports)
  closed₂ : Closed (presentationMatching D₂) (cut ports)
  common : Presentation ℂ (Side (cut ports) false)
  exceptional₀ : Presentation ℂ (Side (cut ports) true)
  exceptional₁ : Presentation ℂ (Side (cut ports) true)
  exceptional₂ : Presentation ℂ (Side (cut ports) true)
  common_det : ∀ e, (common.matrix e).det ≠ 0
  common_matrix_origin : ∀ e, ∃ d, common.matrix e = D₁.matrix d
  exceptional₀_det : ∀ e, (exceptional₀.matrix e).det ≠ 0
  exceptional₁_det : ∀ e, (exceptional₁.matrix e).det ≠ 0
  exceptional₂_det : ∀ e, (exceptional₂.matrix e).det ≠ 0
  common_scalar : common.scalar ≠ 0
  exceptional₀_scalar : exceptional₀.scalar ≠ 0
  exceptional₁_scalar : exceptional₁.scalar ≠ 0
  exceptional₂_scalar : exceptional₂.scalar ≠ 0
  exceptional₀_mate : ∀ p : Side (cut ports) true,
    ((presentationMatching exceptional₀).mate p).val = (presentationMatching D₀).mate p.val
  exceptional₁_mate : ∀ p : Side (cut ports) true,
    ((presentationMatching exceptional₁).mate p).val = (presentationMatching D₁).mate p.val
  exceptional₂_mate : ∀ p : Side (cut ports) true,
    ((presentationMatching exceptional₂).mate p).val = (presentationMatching D₂).mate p.val
  common_mate : ∀ p : Side (cut ports) false,
    ((presentationMatching common).mate p).val = (presentationMatching D₁).mate p.val
  common_nonzero : common.tensor ≠ 0
  factor₀ : ∀ x : P → Bool, D₀.tensor x =
    exceptional₀.tensor (fun p => x p.val) * common.tensor (fun p => x p.val)
  factor₁ : ∀ x : P → Bool, D₁.tensor x =
    exceptional₁.tensor (fun p => x p.val) * common.tensor (fun p => x p.val)
  factor₂ : ∀ x : P → Bool, D₂.tensor x =
    exceptional₂.tensor (fun p => x p.val) * common.tensor (fun p => x p.val)
  span_dimension : Module.finrank ℂ (Submodule.span ℂ
    ({exceptional₀.tensor,exceptional₁.tensor,exceptional₂.tensor} :
      Set (Tensor ℂ (Side (cut ports) true)))) = 2

theorem AlgebraicLocalization.unique_ports {D₀ D₁ D₂ : Presentation ℂ P}
    (L : AlgebraicLocalization D₀ D₁ D₂) (T : Finset P)
    (hT : ∀ p, p ∈ T ↔ (presentationMatching D₀).mate p ≠ (presentationMatching D₁).mate p) :
    T = L.ports := by
  ext p
  rw [hT p,L.support p]

/-- Even the weaker statement that a second four-port set contains every
matching disagreement forces it to be this exact exceptional set. -/
theorem AlgebraicLocalization.unique_of_agreement_outside {D₀ D₁ D₂ : Presentation ℂ P}
    (L : AlgebraicLocalization D₀ D₁ D₂) (T : Finset P) (hcard : T.card = 4)
    (hT : ∀ p, p ∉ T → (presentationMatching D₀).mate p = (presentationMatching D₁).mate p) :
    T = L.ports := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    by_contra hn
    exact ((L.support p).mp hp) (hT p hn)
  · rw [hcard,L.card_ports]

private theorem restricted_not_proportional (D E : Presentation ℂ P) (s : P → Bool)
    (hDc : Closed (presentationMatching D) s) (hEc : Closed (presentationMatching E) s)
    (hD : ∀ e, (D.matrix e).det ≠ 0) (hE : ∀ e, (E.matrix e).det ≠ 0)
    (hcD : D.scalar ≠ 0) (hcE : E.scalar ≠ 0) (p : Side s true)
    (hne : (presentationMatching D).mate p.val ≠ (presentationMatching E).mate p.val) :
    ¬ Proportional (factorPresentation D s true hDc D.scalar).tensor
      (factorPresentation E s true hEc E.scalar).tensor := by
  rintro ⟨c,hc,he⟩
  have hm := matching_eq_of_tensor_smul _ _
    (factorPresentation_det D s true hDc D.scalar hD)
    (factorPresentation_det E s true hEc E.scalar hE) hcD hcE c he
  have hh := congrArg (fun m : Equiv.Perm (Side s true) => (m p).val) hm
  rw [factorPresentation_mate,factorPresentation_mate] at hh
  exact hne hh

/-- Source algebraic localization, derived from three literal nonsingular
matching presentations and their ordinary two-generator span membership.
No localized exceptional set, fixed common factor, or matching alignment is
assumed.  The separate physical realization and complexity claims are not
part of this algebraic theorem. -/
theorem algebraic_localization (D₀ D₁ D₂ : Presentation ℂ P)
    (h₀ : ∀ e, (D₀.matrix e).det ≠ 0) (h₁ : ∀ e, (D₁.matrix e).det ≠ 0)
    (h₂ : ∀ e, (D₂.matrix e).det ≠ 0)
    (hc₀ : D₀.scalar ≠ 0) (hc₁ : D₁.scalar ≠ 0) (hc₂ : D₂.scalar ≠ 0)
    (hne₀₁ : (presentationMatching D₀).mate ≠ (presentationMatching D₁).mate)
    (hne₂₀ : (presentationMatching D₂).mate ≠ (presentationMatching D₀).mate)
    (hne₂₁ : (presentationMatching D₂).mate ≠ (presentationMatching D₁).mate)
    (hline : D₂.tensor ∈ Submodule.span ℂ ({D₀.tensor,D₁.tensor} : Set (Tensor ℂ P))) :
    Nonempty (AlgebraicLocalization D₀ D₁ D₂) := by
  let M₀ := presentationMatching D₀
  let M₁ := presentationMatching D₁
  let M₂ := presentationMatching D₂
  obtain ⟨ht₂,ht₁,ht₀⟩ := presentation_three_cut_triangles D₀ D₁ D₂ h₀ h₁ h₂ hc₀ hc₁ hc₂ hne₂₀ hne₂₁ hline
  obtain ⟨a,b,ha,hb,he⟩ := nonzero_line_coefficients D₀ D₁ D₂ h₀ h₁ h₂ hc₀ hc₁ hc₂ hne₂₀ hne₂₁ hline
  have hex : ∃ p, M₀.mate p ≠ M₁.mate p := by
    by_contra hh
    push Not at hh
    exact hne₀₁ (Equiv.ext hh)
  obtain ⟨p,hp⟩ := hex
  let S := fourPorts M₀ M₁ M₂ p
  let s := cut S
  have hS := fourPorts_card M₀ M₁ M₂ ht₂ ht₁ ht₀ p hp
  have hsupport := fourPorts_disagreement_iff M₀ M₁ M₂ ht₂ ht₁ ht₀ p hp
  obtain ⟨hS₀,hS₁,hS₂⟩ := fourPorts_closed M₀ M₁ M₂ ht₂ ht₁ ht₀ p hp
  have hcl₀ : Closed M₀ s := closed_cut M₀ S hS₀
  have hcl₁ : Closed M₁ s := closed_cut M₁ S hS₁
  have hcl₂ : Closed M₂ s := closed_cut M₂ S hS₂
  let L₀ := factorPresentation D₀ s true hcl₀ D₀.scalar
  let L₁ := factorPresentation D₁ s true hcl₁ D₁.scalar
  let L₂ := factorPresentation D₂ s true hcl₂ D₂.scalar
  let R₀ := factorPresentation D₀ s false hcl₀ 1
  let R₁ := factorPresentation D₁ s false hcl₁ 1
  let R₂ := factorPresentation D₂ s false hcl₂ 1
  have hl₀ : L₀.tensor ≠ 0 := productValue_nonzero _ _ _ (factorPresentation_det D₀ s true hcl₀ _ h₀) hc₀
  have hl₁ : L₁.tensor ≠ 0 := productValue_nonzero _ _ _ (factorPresentation_det D₁ s true hcl₁ _ h₁) hc₁
  have hl₂ : L₂.tensor ≠ 0 := productValue_nonzero _ _ _ (factorPresentation_det D₂ s true hcl₂ _ h₂) hc₂
  have hr₀ : R₀.tensor ≠ 0 := productValue_nonzero _ _ _ (factorPresentation_det D₀ s false hcl₀ _ h₀) one_ne_zero
  have hr₁ : R₁.tensor ≠ 0 := productValue_nonzero _ _ _ (factorPresentation_det D₁ s false hcl₁ _ h₁) one_ne_zero
  have hr₂ : R₂.tensor ≠ 0 := productValue_nonzero _ _ _ (factorPresentation_det D₂ s false hcl₂ _ h₂) one_ne_zero
  have hsep : ¬ Proportional L₀.tensor L₁.tensor := by
    apply restricted_not_proportional D₀ D₁ s hcl₀ hcl₁ h₀ h₁ hc₀ hc₁
      ⟨p,(cut_true S p).mpr (by simp [S,fourPorts])⟩ hp
  have hout : Matrix.vecMulVec L₂.tensor R₂.tensor =
      a • Matrix.vecMulVec L₀.tensor R₀.tensor + b • Matrix.vecMulVec L₁.tensor R₁.tensor := by
    have hh := congrArg (flatten s) he
    rw [flatten_add,flatten_smul,flatten_smul,flatten_eq_outer_factors D₀ s hcl₀,
      flatten_eq_outer_factors D₁ s hcl₁,flatten_eq_outer_factors D₂ s hcl₂] at hh
    simpa only [L₀,L₁,L₂,R₀,R₁,R₂,factorPresentation_tensor] using hh
  obtain ⟨s₀,s₂,hs₀,hs₂,hR₀,hR₂,hE⟩ := three_split_tensors_common_complement
    L₀.tensor L₁.tensor L₂.tensor R₀.tensor R₁.tensor R₂.tensor
    hl₀ hl₁ hl₂ hr₀ hr₁ hr₂ hsep a b ha hb hout
  let E₀ := factorPresentation D₀ s true hcl₀ (s₀*D₀.scalar)
  let E₂ := factorPresentation D₂ s true hcl₂ (s₂*D₂.scalar)
  have he₀ : E₀.tensor = s₀ • L₀.tensor := by
    simp only [E₀,L₀,factorPresentation_tensor,factor_smul]
  have he₂ : E₂.tensor = s₂ • L₂.tensor := by
    simp only [E₂,L₂,factorPresentation_tensor,factor_smul]
  have heline : E₂.tensor = a • E₀.tensor + b • L₁.tensor := by rw [he₀,he₂]; exact hE
  have hsepn : ¬ Proportional E₀.tensor L₁.tensor := by
    intro hh
    apply hsep
    apply Proportional.trans (v := E₀.tensor) _ hh
    refine ⟨s₀⁻¹,inv_ne_zero hs₀,?_⟩
    rw [he₀,smul_smul,inv_mul_cancel₀ hs₀,one_smul]
  have hen₀ : E₀.tensor ≠ 0 := by rw [he₀]; exact smul_ne_zero hs₀ hl₀
  refine ⟨{
    ports := S
    card_ports := hS
    support := hsupport
    inside := ?_
    outside := ?_
    closed₀ := hcl₀
    closed₁ := hcl₁
    closed₂ := hcl₂
    common := R₁
    exceptional₀ := E₀
    exceptional₁ := L₁
    exceptional₂ := E₂
    common_det := factorPresentation_det D₁ s false hcl₁ 1 h₁
    common_matrix_origin := fun e => ⟨_,rfl⟩
    exceptional₀_det := factorPresentation_det D₀ s true hcl₀ _ h₀
    exceptional₁_det := factorPresentation_det D₁ s true hcl₁ _ h₁
    exceptional₂_det := factorPresentation_det D₂ s true hcl₂ _ h₂
    common_scalar := one_ne_zero
    exceptional₀_scalar := mul_ne_zero hs₀ hc₀
    exceptional₁_scalar := hc₁
    exceptional₂_scalar := mul_ne_zero hs₂ hc₂
    exceptional₀_mate := factorPresentation_mate D₀ s true hcl₀ _
    exceptional₁_mate := factorPresentation_mate D₁ s true hcl₁ _
    exceptional₂_mate := factorPresentation_mate D₂ s true hcl₂ _
    common_mate := factorPresentation_mate D₁ s false hcl₁ _
    common_nonzero := hr₁
    factor₀ := ?_
    factor₁ := ?_
    factor₂ := ?_
    span_dimension := nonproportional_span_triple_finrank E₀.tensor L₁.tensor E₂.tensor
      hen₀ hl₁ hsepn a b heline
  }⟩
  · intro q hq
    have hh := local_four_port_relations M₀ M₁ M₂ ht₂ ht₁ ht₀ q ((hsupport q).mp hq)
    exact ⟨hh.1,hh.2.1⟩
  · intro q hq
    have hh := agreement_outside_fourPorts M₀ M₁ M₂ ht₂ ht₁ ht₀ p hp q hq
    exact ⟨hh,edge_of_two M₀ M₁ M₂ ht₂ q (M₀.mate q) rfl hh.symm⟩
  · intro x
    have hh : D₀.tensor x = L₀.tensor (fun p => x p.val) * R₀.tensor (fun p => x p.val) := by
      rw [show L₀.tensor = factor M₀ s true D₀.matrix D₀.scalar from
        factorPresentation_tensor D₀ s true hcl₀ D₀.scalar,
        show R₀.tensor = factor M₀ s false D₀.matrix 1 from
        factorPresentation_tensor D₀ s false hcl₀ 1]
      exact product_eq_factors M₀ s hcl₀ D₀.matrix D₀.scalar x
    rw [hh,hR₀,he₀]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  · intro x
    rw [show L₁.tensor = factor M₁ s true D₁.matrix D₁.scalar from
      factorPresentation_tensor D₁ s true hcl₁ D₁.scalar,
      show R₁.tensor = factor M₁ s false D₁.matrix 1 from
      factorPresentation_tensor D₁ s false hcl₁ 1]
    exact product_eq_factors M₁ s hcl₁ D₁.matrix D₁.scalar x
  · intro x
    have hh : D₂.tensor x = L₂.tensor (fun p => x p.val) * R₂.tensor (fun p => x p.val) := by
      rw [show L₂.tensor = factor M₂ s true D₂.matrix D₂.scalar from
        factorPresentation_tensor D₂ s true hcl₂ D₂.scalar,
        show R₂.tensor = factor M₂ s false D₂.matrix 1 from
        factorPresentation_tensor D₂ s false hcl₂ 1]
      exact product_eq_factors M₂ s hcl₂ D₂.matrix D₂.scalar x
    rw [hh,hR₂,he₂]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring

end Holant.Platonic.RainbowLocalization
