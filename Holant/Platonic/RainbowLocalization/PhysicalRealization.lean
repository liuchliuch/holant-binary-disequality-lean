import Holant.Platonic.RainbowLocalization.PhysicalOccurrence
import Holant.Platonic.RainbowLocalization.PhysicalCanonicalDeck
import Holant.OpenNetworkComposition.ProjectiveSubstitution

/-! Actual substitution over the retained family, with its nonzero global
normalization witness exposed.  No computational reduction is inferred. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure
variable {P : Type*} [Fintype P] [DecidableEq P] {n : ℕ}
variable {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
variable {D₀ D₁ D₂ : Presentation ℂ P}

/-- Genuine projective realizability of the computed localized graph over
the original retained family, from the actual original and kernel gadgets. -/
theorem localization_realizesUpTo (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges → D) (f : Signature ℂ n) (hf : Gadget.Realizes Λ .disequality f) :
    Gadget.RealizesUpTo Λ .disequality (localizationSignature A L p C f) :=
  OpenNetworkComposition.realizes_network_upTo Λ (localizationNetwork A L p C f)
    (localization_vertices_realizable A L p C f hf) (localization_edges_native A L p C f) (by norm_num)

/-- An exact actual six-port representative is obtained with the explicit
nonzero scalar returned by gadget substitution. -/
theorem localization_actual_representative (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges → D) (f : Signature ℂ n) (hf : Gadget.Realizes Λ .disequality f) :
    ∃ c : ℂ, c ≠ 0 ∧ Gadget.Realizes Λ .disequality (c • localizationSignature A L p C f) := by
  obtain ⟨c,hc,hr⟩ := localization_realizesUpTo A L p C f hf
  exact ⟨c,hc,hr⟩

theorem contractPair_tensor_smul {Q : Type*} [DecidableEq Q]
    (u v : Q) (K : Kernel ℂ) (f : Tensor ℂ Q) (c : ℂ) :
    contractPair u v K (c • f) = c • contractPair u v K f := by
  funext x
  simp only [contractPair,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
  ring

theorem quaternary_of_safe_card (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (f : Signature ℂ 6) (u v : Fin 6) (huv : u ≠ v) (K : Kernel ℂ)
    (h : MatchingOrZero G (contractPair u v K f)) :
    contractPair u v K f = 0 ∨ ∃ M : Presentation ℂ (Remaining u v),
      M.edges = 2 ∧ M.scalar ≠ 0 ∧ (∀ e, (M.matrix e).det ≠ 0 ∧ SafeBinary G (M.matrix e)) ∧
      contractPair u v K f = M.tensor := by
  rcases h with hz | ⟨M,hM,hc,he⟩
  · exact Or.inl hz
  · have hcM := (presentationMatching M).port_card
    rw [remaining_six_card u v huv] at hcM
    have hm : M.edges = 2 := by change 4 = 2 * M.edges at hcM; omega
    exact Or.inr ⟨M,hm,hc,fun e => ⟨SafeBinary.nonsingular hG (hM e),hM e⟩,he⟩

end Holant.Platonic.RainbowLocalization.Physical
