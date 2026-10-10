import Holant.Platonic.RankDeficientLocalization.PhysicalRank

/-! The matching-changing branch of source Lemma9.11, including the exact
kernel-deleted line construction, all-card inheritance, intrinsic rank bounds,
and the actual finite-family polynomial reduction from the one-ancestor graph.
This file does not assert the fixed-matching proper-factor branch or A.24's
normalization-to-six-output classification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RankDeficientLocalization
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.RainbowOrbit
open Holant.Certificates.MatchingContractionClosure
open Holant.Platonic.RainbowLocalization Holant.Platonic.RainbowLocalization.Physical
variable {P : Type*} [Fintype P] [DecidableEq P] {n s : ℕ}
variable {arity : ℕ→ℕ} {D : Set (Kernel ℂ)}

theorem nonsingular_card_of_matching (G : Set (Binary (K := ℂ)))
    (hG : ProjectiveMatrixGroup G) (F : Tensor ℂ P) (hF : MatchingOrZero G F) :
    F=0 ∨ Nonempty (NonsingularCard F) := by
  rcases hF with hz|⟨M,hM,hc,he⟩
  · exact Or.inl hz
  · exact Or.inr ⟨⟨M,fun e => SafeBinary.nonsingular hG (hM e),hc,he⟩⟩

/-- Safe ancestor cards imply the exact uncoloured geometric card hypothesis
at any recorded ordered pair, in its literal remaining physical coordinates. -/
theorem nonsingular_actual_domain_cards
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (p : Bool ⊕ P ≃ Fin n) (f : Signature ℂ n)
    (U : Fin s→Kernel ℂ) (hUD : ∀i,U i∈D)
    (hdeck : ∀u v : Fin n,u≠v→∀K∈D,MatchingOrZero G (contractPair u v K f)) :
    ∀i,cardMap p f (U i)=0 ∨ Nonempty (NonsingularCard (cardMap p f (U i))) := by
  intro i
  apply nonsingular_card_of_matching G hG
  rw [cardMap_eq_contractPair]
  exact (hdeck _ _ (pair_distinct p) _ (hUD i)).reindex (pairRemaining p).symm

/-- The concrete mixed branch: literal full domain line, exact closure graph,
nonzero selected cards, intrinsic ranks, and a real encoded oracle machine. -/
def MixedLocalizationResult
    (signatures : (i : Fin s)→Signature ℂ (arity i.val))
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x))
    (A : ActualKernelLift (indexedRetainedFamily arity signatures) D)
    (p : Bool ⊕ P ≃ Fin n) (f : Signature ℂ n)
    (G : Set (Binary (K := ℂ))) (g : PlatonicModel) (e : Mat ≃ₗ[ℂ] Mat) : Prop :=
    ∃R : RainbowDomainLine (cardMap p f) (fun i => e (representative g i)),
      ∃(L : AlgebraicLocalization R.card₀.presentation R.card₁.presentation R.card₂.presentation)
        (C : Fin L.common.edges→D),
      localizationScale A L C≠0 ∧ localizationSignature A L p C f≠0 ∧
      cardMap (sixPortOrder L) (localizationSignature A L p C f) (e (representative g R.first))=
        localizationScale A L C • L.exceptional₀.tensor ∧
      cardMap (sixPortOrder L) (localizationSignature A L p C f) (e (representative g R.second))=
        localizationScale A L C • L.exceptional₁.tensor ∧
      cardMap (sixPortOrder L) (localizationSignature A L p C f) (e (representative g R.third))=
        localizationScale A L C • L.exceptional₂.tensor ∧
      2≤Module.finrank ℂ (cardMap (sixPortOrder L) (localizationSignature A L p C f)).range ∧
      Module.finrank ℂ (cardMap (sixPortOrder L) (localizationSignature A L p C f)).range≤
        Module.finrank ℂ (cardMap p f).range ∧
      Module.finrank ℂ (cardMap p f).range≤4 ∧
      (localizationNetwork A L p C f).shape.vertices=(n-6)/2+1 ∧
      (localizationNetwork A L p C f).shape.edges=2*((n-6)/2) ∧
      Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality
        (localizationSignature A L p C f) ∧
      EncodedNativeAdjoin signatures halg (localizationSignature A L p C f) ∧
      ∀u v : Fin 6,u≠v→∀K∈D,
        contractPair u v K (localizationSignature A L p C f)=0 ∨
        ∃M : Presentation ℂ (Remaining u v),M.edges=2 ∧ M.scalar≠0 ∧
          (∀j,(M.matrix j).det≠0 ∧ SafeBinary G (M.matrix j)) ∧
          contractPair u v K (localizationSignature A L p C f)=M.tensor

/-- The source's mixed-card route, with source dimension/rank and all actual
physical and encoded provenance. Nothing about a smaller coloured graph or an
already normalized rainbow line is assumed. -/
theorem source_mixed_localization_encoded
    (signatures : (i : Fin s)→Signature ℂ (arity i.val))
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x))
    (A : ActualKernelLift (indexedRetainedFamily arity signatures) D)
    (p : Bool ⊕ P ≃ Fin n) (f : Signature ℂ n)
    (hf : (⟨n,f⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (hb : ∀K : D,(⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ)∈
      indexedRetainedFamily arity signatures)
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (Holant.Certificates.MatchingContractionClosure.X : Binary (K := ℂ))∈G) (hrev : ReversalStable G)
    (hD : D⊆G) (hcomplete : CompleteKernelRepresentatives G D)
    (hspan : Submodule.span ℂ D=⊤)
    (hdeck : ∀u v : Fin n,u<v→∀K∈D,MatchingOrZero G (contractPair u v K f))
    (g : PlatonicModel) (e : Mat ≃ₗ[ℂ] Mat)
    (hactual : ∀i,e (representative g i)∈D)
    (hr : 2≤Module.finrank ℂ (cardMap p f).range)
    (hmix : MixedCards (cardMap p f) (fun i => e (representative g i))) :
    MixedLocalizationResult signatures halg A p f G g e := by
  have hordered := all_orderings_of_canonical G hG hX hrev D hD hcomplete f hdeck
  have hcards := nonsingular_actual_domain_cards G hG p f _ hactual hordered
  obtain ⟨R⟩ := platonic_rainbow_domain_line g e (cardMap p f) hr hcards hmix
  obtain ⟨L,C,hs,hn,h₀,h₁,h₂,hv,he,hreal,henc,hall⟩ :=
    source_rainbow_localization_encoded signatures halg A p f hf hb G hG hX hrev hD hcomplete hspan hdeck
      _ _ _ (hactual R.first) (hactual R.second) (hactual R.third) R.third_mem
      R.card₀.value R.card₁.value R.card₂.value
      R.card₀.det_ne_zero R.card₁.det_ne_zero R.card₂.det_ne_zero
      R.card₀.scalar_ne_zero R.card₁.scalar_ne_zero R.card₂.scalar_ne_zero
      R.different₀₁ R.different₂₀ R.different₂₁
  obtain ⟨hrlow,hrup,hrfour⟩ := localization_rank_bounds A L p C f hs _ _ h₀ h₁
  exact ⟨R,L,C,hs,hn,h₀,h₁,h₂,hrlow,hrup,hrfour,hv,he,hreal,henc,hall⟩

end Holant.Platonic.RankDeficientLocalization
