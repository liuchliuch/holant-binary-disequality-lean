import Holant.Platonic.RainbowLocalization.PhysicalSource

/-! The three retained actual cards remain nonzero and projectively distinct. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure MatchingCut
open Holant.Certificates.RainbowOrbit (Proportional)
variable {P : Type*} [Fintype P] [DecidableEq P]
variable {D₀ D₁ D₂ : Presentation ℂ P}

theorem exceptional_matchings_distinct (L : AlgebraicLocalization D₀ D₁ D₂) :
    (presentationMatching L.exceptional₀).mate ≠ (presentationMatching L.exceptional₁).mate ∧
    (presentationMatching L.exceptional₂).mate ≠ (presentationMatching L.exceptional₀).mate ∧
    (presentationMatching L.exceptional₂).mate ≠ (presentationMatching L.exceptional₁).mate := by
  have hn : Nonempty (Side (cut L.ports) true) := Fintype.card_pos_iff.mp (by
    rw [side_cut_card,L.card_ports]; decide)
  obtain ⟨p⟩ := hn
  have hp : p.val ∈ L.ports := (cut_true L.ports p.val).mp p.property
  have h₀₁ := (L.support p.val).mp hp
  have h₂₀ := (L.inside p.val hp).1
  have h₂₁ := (L.inside p.val hp).2
  refine ⟨?_,?_,?_⟩
  · intro h
    have hh := congrArg (fun m : Equiv.Perm (Side (cut L.ports) true) => (m p).val) h
    rw [L.exceptional₀_mate,L.exceptional₁_mate] at hh
    exact h₀₁ hh
  · intro h
    have hh := congrArg (fun m : Equiv.Perm (Side (cut L.ports) true) => (m p).val) h
    rw [L.exceptional₂_mate,L.exceptional₀_mate] at hh
    exact h₂₀ hh
  · intro h
    have hh := congrArg (fun m : Equiv.Perm (Side (cut L.ports) true) => (m p).val) h
    rw [L.exceptional₂_mate,L.exceptional₁_mate] at hh
    exact h₂₁ hh

theorem exceptional_projectively_distinct (L : AlgebraicLocalization D₀ D₁ D₂) :
    ¬ Proportional L.exceptional₀.tensor L.exceptional₁.tensor ∧
    ¬ Proportional L.exceptional₂.tensor L.exceptional₀.tensor ∧
    ¬ Proportional L.exceptional₂.tensor L.exceptional₁.tensor := by
  obtain ⟨h₀₁,h₂₀,h₂₁⟩ := exceptional_matchings_distinct L
  refine ⟨?_,?_,?_⟩
  · rintro ⟨c,hc,he⟩
    exact h₀₁ (matching_eq_of_tensor_smul _ _ L.exceptional₀_det L.exceptional₁_det
      L.exceptional₀_scalar L.exceptional₁_scalar c he)
  · rintro ⟨c,hc,he⟩
    exact h₂₀ (matching_eq_of_tensor_smul _ _ L.exceptional₂_det L.exceptional₀_det
      L.exceptional₂_scalar L.exceptional₀_scalar c he)
  · rintro ⟨c,hc,he⟩
    exact h₂₁ (matching_eq_of_tensor_smul _ _ L.exceptional₂_det L.exceptional₁_det
      L.exceptional₂_scalar L.exceptional₁_scalar c he)

variable {n : ℕ} {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
variable {A : ActualKernelLift Λ D} {G : Set (Binary (K := ℂ))}
variable {p : Bool ⊕ P ≃ Fin n} {f : Signature ℂ n} {K₀ K₁ K₂ : Kernel ℂ}

theorem PhysicalLocalization.selected_nonzero
    (T : PhysicalLocalization A G p f K₀ K₁ K₂ D₀ D₁ D₂) :
    cardMap (sixPortOrder T.algebraic) T.signature K₀ ≠ 0 ∧
    cardMap (sixPortOrder T.algebraic) T.signature K₁ ≠ 0 ∧
    cardMap (sixPortOrder T.algebraic) T.signature K₂ ≠ 0 := by
  rw [T.card₀,T.card₁,T.card₂]
  exact ⟨smul_ne_zero T.surviving_scale_ne_zero (productValue_nonzero _ _ _
      T.algebraic.exceptional₀_det T.algebraic.exceptional₀_scalar),
    smul_ne_zero T.surviving_scale_ne_zero (productValue_nonzero _ _ _
      T.algebraic.exceptional₁_det T.algebraic.exceptional₁_scalar),
    smul_ne_zero T.surviving_scale_ne_zero (productValue_nonzero _ _ _
      T.algebraic.exceptional₂_det T.algebraic.exceptional₂_scalar)⟩

theorem PhysicalLocalization.selected_projectively_distinct
    (T : PhysicalLocalization A G p f K₀ K₁ K₂ D₀ D₁ D₂) :
    ¬ Proportional (cardMap (sixPortOrder T.algebraic) T.signature K₀)
      (cardMap (sixPortOrder T.algebraic) T.signature K₁) ∧
    ¬ Proportional (cardMap (sixPortOrder T.algebraic) T.signature K₂)
      (cardMap (sixPortOrder T.algebraic) T.signature K₀) ∧
    ¬ Proportional (cardMap (sixPortOrder T.algebraic) T.signature K₂)
      (cardMap (sixPortOrder T.algebraic) T.signature K₁) := by
  have h₀ : Proportional (cardMap (sixPortOrder T.algebraic) T.signature K₀) T.algebraic.exceptional₀.tensor :=
    ⟨_,T.surviving_scale_ne_zero,T.card₀⟩
  have h₁ : Proportional (cardMap (sixPortOrder T.algebraic) T.signature K₁) T.algebraic.exceptional₁.tensor :=
    ⟨_,T.surviving_scale_ne_zero,T.card₁⟩
  have h₂ : Proportional (cardMap (sixPortOrder T.algebraic) T.signature K₂) T.algebraic.exceptional₂.tensor :=
    ⟨_,T.surviving_scale_ne_zero,T.card₂⟩
  obtain ⟨h₀₁,h₂₀,h₂₁⟩ := exceptional_projectively_distinct T.algebraic
  exact ⟨fun h => h₀₁ (h₀.symm.trans (h.trans h₁)),
    fun h => h₂₀ (h₂.symm.trans (h.trans h₀)),fun h => h₂₁ (h₂.symm.trans (h.trans h₁))⟩

end Holant.Platonic.RainbowLocalization.Physical
