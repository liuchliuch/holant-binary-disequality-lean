import Holant.Platonic.RankDeficientLocalization.ActualDomain
import Holant.Platonic.RankDeficientLocalization.SourceEncoded

/-! Source Lemma9.11: the complete prioritized structural dichotomy. The
common-matching branch reconstructs a genuine proper factor on original ports.
The mixed branch constructs the literal one-ancestor six-port graph, all actual
safe cards, exact intrinsic rank bounds and a polynomial encoded reduction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RankDeficientLocalization
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.RainbowOrbit
open Holant.Certificates.MatchingContractionClosure
open Holant.Platonic.RainbowLocalization Holant.Platonic.RainbowLocalization.Physical
variable {P : Type*} [Fintype P] [DecidableEq P] {n s : ℕ}
variable {arity : ℕ→ℕ} {D : Set (Kernel ℂ)}

/-- General representative-scaled formulation. Every actual kernel is covered
by the full configuration, and the first branch is selected whenever available. -/
theorem source_high_arity_localization_with_dictionary
    (signatures : (i : Fin s)→Signature ℂ (arity i.val))
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x))
    (A : ActualKernelLift (indexedRetainedFamily arity signatures) D)
    (p : Bool ⊕ P ≃ Fin n) (f : Signature ℂ n)
    (hf : (⟨n,f⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (hfn : f≠0) (hn : 6≤n)
    (hb : ∀K : D,(⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ)∈
      indexedRetainedFamily arity signatures)
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (Holant.Certificates.MatchingContractionClosure.X : Binary (K := ℂ))∈G)
    (hrev : ReversalStable G) (hD : D⊆G) (hcomplete : CompleteKernelRepresentatives G D)
    (hspan : Submodule.span ℂ D=⊤)
    (hdeck : ∀u v : Fin n,u<v→∀K∈D,MatchingOrZero G (contractPair u v K f))
    (g : PlatonicModel) (e : Mat≃ₗ[ℂ]Mat)
    (hactual : ∀i,e (representative g i)∈D)
    (hcover : ∀K∈D,∃i : Fin (size g),∃c : ℂ,c≠0 ∧ K=c • e (representative g i))
    (hr : 2≤Module.finrank ℂ (cardMap p f).range) :
    (CommonActualMatching (cardMap p f) D ∧ Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor f) ∨
    (¬CommonActualMatching (cardMap p f) D ∧ MixedLocalizationResult signatures halg A p f G g e) := by
  classical
  have hordered := all_orderings_of_canonical G hG hX hrev D hD hcomplete f hdeck
  have hcards := nonsingular_actual_domain_cards G hG p f _ hactual hordered
  have hiff := common_actual_iff_domain g e (cardMap p f) D hactual hcover hcards
  by_cases hcommon : CommonActualMatching (cardMap p f) D
  · exact Or.inl ⟨hcommon,common_matching_proper_factor g e p f hfn hn hr hcards (hiff.mp hcommon)⟩
  · refine Or.inr ⟨hcommon,?_⟩
    have hmix : MixedCards (cardMap p f) (fun i => e (representative g i)) := by
      rcases platonic_ruling_or_rainbow g e (cardMap p f) hr hcards with hm | hR
      · exact (hcommon (hiff.mpr hm)).elim
      · obtain ⟨R⟩ := hR
        exact ⟨R.first,R.second,R.card₀,R.card₁,R.different₀₁⟩
    exact source_mixed_localization_encoded signatures halg A p f hf hb G hG hX hrev hD hcomplete
      hspan hdeck g e hactual hr hmix

/-- Source9.11 on the literal full actual Platonic representative set. There
is no coverage hypothesis, precomputed colouring, reduced graph, factor-access
oracle, reconstruction premise or supplied complexity reduction. The state
hypotheses retain the actual binary representatives and their nonzero scales. -/
theorem source_high_arity_localization
    (g : PlatonicModel) (e : Mat≃ₗ[ℂ]Mat)
    (signatures : (i : Fin s)→Signature ℂ (arity i.val))
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x))
    (A : ActualKernelLift (indexedRetainedFamily arity signatures) (actualDomain g e))
    (p : Bool ⊕ P ≃ Fin n) (f : Signature ℂ n)
    (hf : (⟨n,f⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (hfn : f≠0) (hn : 6≤n)
    (hb : ∀K : actualDomain g e,(⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ)∈
      indexedRetainedFamily arity signatures)
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (Holant.Certificates.MatchingContractionClosure.X : Binary (K := ℂ))∈G)
    (hrev : ReversalStable G) (hD : actualDomain g e⊆G)
    (hcomplete : CompleteKernelRepresentatives G (actualDomain g e))
    (hdeck : ∀u v : Fin n,u<v→∀K∈actualDomain g e,MatchingOrZero G (contractPair u v K f))
    (hr : 2≤Module.finrank ℂ (cardMap p f).range) :
    (CommonActualMatching (cardMap p f) (actualDomain g e) ∧
      Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor f) ∨
    (¬CommonActualMatching (cardMap p f) (actualDomain g e) ∧
      MixedLocalizationResult signatures halg A p f G g e) :=
  source_high_arity_localization_with_dictionary signatures halg A p f hf hfn hn hb G hG hX hrev hD
    hcomplete (actualDomain_span g e) hdeck g e (actualDomain_member g e) (actualDomain_cover g e) hr

end Holant.Platonic.RankDeficientLocalization
