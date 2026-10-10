import Holant.Platonic.FixedMatchingRuling.ReconstructionFactor
import Holant.Platonic.FixedMatchingRuling.TetrahedralExtension

/-! The physical reconstruction clause of source Lemma 9.6, obtained from the
actual twelve quaternion test cards and the original physical port partition. -/
noncomputable section
namespace Holant.Platonic.FixedMatchingRuling.Physical
open Holant Holant.Certificates.MatchingProductBridge
variable {M P : Type*} [Fintype M] [DecidableEq M]

/-- Actual tetrahedral test cards in a fixed residual block Segre cone force a
proper tensor factor of the original nonzero physical signature. The factors
are reconstructed on the original ports; no factor gadget is assumed. -/
theorem proper_factor_of_tetrahedral_cards (ℓ : M → ℕ) (hℓ : ∀ e, 0 < ℓ e)
    (p : (Bool ⊕ (j : M) × Fin (ℓ j)) ≃ P) (f : Tensor ℂ P)
    (hf : f ≠ 0) (hM : 2 ≤ Fintype.card M)
    (htest : ∀ K, tetrahedralBase K → Segre.TensorPureOrZero (cardMap ℓ p f K)) :
    Pauli.ExoticKlein.Fiber.HasProperTensorFactor f := by
  have : Nonempty M := Fintype.card_pos_iff.mp (by omega)
  have hΦ : cardMap ℓ p f ≠ 0 := fun h => hf ((cardMap_eq_zero_iff ℓ p f).mp h)
  obtain ⟨e,U,ψ,_,hruling⟩ := tetrahedral_fixed_matching_ruling (cardMap ℓ p f) hΦ htest
  exact proper_factor_of_ruling ℓ hℓ p f hΦ hM e U ψ hruling

/-- Source Lemma 9.6's physical conclusion for any projective test set D
containing nonzero representatives of the twelve tetrahedral points. -/
theorem proper_factor_of_projective_cards (ℓ : M → ℕ) (hℓ : ∀ e, 0 < ℓ e)
    (p : (Bool ⊕ (j : M) × Fin (ℓ j)) ≃ P) (f : Tensor ℂ P)
    (hf : f ≠ 0) (hM : 2 ≤ Fintype.card M) (D : Set Binary)
    (hcontains : ∀ K, tetrahedralBase K → ∃ c : ℂ, c ≠ 0 ∧ c • K ∈ D)
    (htest : ∀ K ∈ D, Segre.TensorPureOrZero (cardMap ℓ p f K)) :
    Pauli.ExoticKlein.Fiber.HasProperTensorFactor f := by
  have : Nonempty M := Fintype.card_pos_iff.mp (by omega)
  have hΦ : cardMap ℓ p f ≠ 0 := fun h => hf ((cardMap_eq_zero_iff ℓ p f).mp h)
  obtain ⟨e,U,ψ,_,hruling⟩ :=
    source_projective_fixed_matching_ruling D (cardMap ℓ p f) hΦ hcontains htest
  exact proper_factor_of_ruling ℓ hℓ p f hΦ hM e U ψ hruling

end Holant.Platonic.FixedMatchingRuling.Physical
