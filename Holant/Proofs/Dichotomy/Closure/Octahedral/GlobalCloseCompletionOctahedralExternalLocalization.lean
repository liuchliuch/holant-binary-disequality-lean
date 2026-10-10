import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralExternalDeck
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralExternalNoRainbow
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicLocalizationCards
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicHigherRank

/-! A genuine external-T rainbow at any arity localizes through actual
safe closure kernels to the forbidden four-port rainbow. Every inherited
card remains in the exact external-T matching cone. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalLocalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.RainbowOrbit
open Holant.Platonic.RankDeficientLocalization
open Holant.Platonic.RainbowLocalization Holant.Platonic.RainbowLocalization.Physical
open Holant.Platonic.RainbowLocalization.MatchingCut
open Holant.Platonic.TetrahedralLocalization Holant.Platonic.StabilizerShortening
open GlobalCloseCompletionTetrahedralSix.Normalization
open GlobalCloseCompletionPlatonicCardReindex GlobalCloseCompletionPlatonicLocalizationCards
open GlobalCloseCompletionOctahedralExternalDeck
variable {P : Type*} [Fintype P] [DecidableEq P]
variable {D₀ D₁ D₂ : Presentation ℂ P}

theorem localized_mixed {n : ℕ} (p : Bool ⊕ P≃Fin n) (f : Signature ℂ n)
    (R : RainbowDomainLine (cardMap p f) (fun i=>dictionary (representative .tetrahedral i)))
    (L : AlgebraicLocalization R.card₀.presentation R.card₁.presentation R.card₂.presentation)
    (q : Signature ℂ 6) (c : ℂ) (hc : c≠0)
    (h₀ : cardMap (sixPortOrder L) q (dictionary (representative .tetrahedral R.first))=c • L.exceptional₀.tensor)
    (h₁ : cardMap (sixPortOrder L) q (dictionary (representative .tetrahedral R.second))=c • L.exceptional₁.tensor) :
    MixedCards (actualMap q) (fun i=>dictionary (representative .tetrahedral i)) := by
  let e := residualEquiv L
  have he₀ : actualMap q (dictionary (representative .tetrahedral R.first))=c • Tensor.reindex e L.exceptional₀.tensor := by
    rw [actualMap_reindex L,h₀]
    rfl
  have he₁ : actualMap q (dictionary (representative .tetrahedral R.second))=c • Tensor.reindex e L.exceptional₁.tensor := by
    rw [actualMap_reindex L,h₁]
    rfl
  let E₀ := cardOfScaledReindex L.exceptional₀ e c hc L.exceptional₀_det L.exceptional₀_scalar _ he₀
  let E₁ := cardOfScaledReindex L.exceptional₁ e c hc L.exceptional₁_det L.exceptional₁_scalar _ he₁
  refine ⟨R.first,R.second,E₀,E₁,?_⟩
  exact scaled_matching_ne L.exceptional₀ L.exceptional₁ e c hc
    L.exceptional₀_det L.exceptional₁_det L.exceptional₀_scalar L.exceptional₁_scalar _ _ he₀ he₁
    (GlobalCloseCompletionPlatonicLocalizationCards.exceptional_matching_ne L)

theorem cone_of_matching (q : FourTensor) (hq : MatchingOrZero directions q) :
    GlobalCloseCompletionOctahedralExternalCone.Cone q := by
  rcases hq with hz | ⟨M,hM,_,rfl⟩
  · exact Or.inl hz
  · exact GlobalCloseCompletionOctahedralExternalCone.presentation M
      (fun e=>(directions_safe_iff _).mp (hM e))

theorem no_rainbow_coefficients {n : ℕ}
    (p : Bool ⊕ P≃Fin n) (f : Signature ℂ n)
    (hdeck : ∀u v : Fin n,u≠v→∀K,RainbowOrbit.External.Direction K→
      MatchingOrZero directions (contractPair u v K f))
    (R : RainbowDomainLine (cardMap p f) (fun i=>dictionary (representative .tetrahedral i))) : False := by
  let G := directions
  have hG := directions_group
  have hX := directions_X
  have hrev := directions_reversal
  have value₀ : cardMap p f (dictionary (representative .tetrahedral R.first))=R.card₀.presentation.tensor :=
    R.card₀.value
  have value₁ : cardMap p f (dictionary (representative .tetrahedral R.second))=R.card₁.presentation.tensor :=
    R.card₁.value
  have value₂ : cardMap p f (dictionary (representative .tetrahedral R.third))=R.card₂.presentation.tensor :=
    R.card₂.value
  have hline := card_line_from_domain p f _ _ _ R.third_mem
  rw [value₀,value₁,value₂] at hline
  obtain ⟨L⟩ := algebraic_localization R.card₀.presentation R.card₁.presentation R.card₂.presentation
    R.card₀.det_ne_zero R.card₁.det_ne_zero R.card₂.det_ne_zero
    R.card₀.scalar_ne_zero R.card₁.scalar_ne_zero R.card₂.scalar_ne_zero
    R.different₀₁ R.different₂₀ R.different₂₁ hline
  have hn (e : Fin L.common.edges) : L.common.matrix e≠0 := by
    intro he
    exact L.common_det e (by rw [he];simp)
  obtain ⟨C,hC,_,hprod⟩ := choose_actual_closing_kernels G directions_span L.common.matrix hn
  have hs : closureScale L C≠0 := mul_ne_zero L.common_scalar hprod
  let q := contractCollection (originalClosurePorts L p) C f
  have h₀ : cardMap (sixPortOrder L) q (dictionary (representative .tetrahedral R.first))=
      closureScale L C • L.exceptional₀.tensor := by
    calc
      _ = contractCollection (localizedPorts L) C
          (cardMap p f (dictionary (representative .tetrahedral R.first))) :=
        cardMap_full_closure p (localizedPorts L) (sixPortOrder L) C f _
      _ = contractCollection (localizedPorts L) C R.card₀.presentation.tensor :=
        congrArg (fun F : Tensor ℂ P => contractCollection (localizedPorts L) C F) value₀
      _ = _ := close_factorized L C _ _ L.factor₀
  have h₁ : cardMap (sixPortOrder L) q (dictionary (representative .tetrahedral R.second))=
      closureScale L C • L.exceptional₁.tensor := by
    calc
      _ = contractCollection (localizedPorts L) C
          (cardMap p f (dictionary (representative .tetrahedral R.second))) :=
        cardMap_full_closure p (localizedPorts L) (sixPortOrder L) C f _
      _ = contractCollection (localizedPorts L) C R.card₁.presentation.tensor :=
        congrArg (fun F : Tensor ℂ P => contractCollection (localizedPorts L) C F) value₁
      _ = _ := close_factorized L C _ _ L.factor₁
  have hc : ∀e,SafeBinary G (C e) := fun e=>(directions_safe_iff _).mpr (hC e)
  have hall := all_cards_after_collection G hG hX hrev G (originalClosurePorts L p) C f hc hdeck
  have cones : ∀i : Fin 12,GlobalCloseCompletionOctahedralExternalCone.Cone
      (actualMap q (dictionary (representative .tetrahedral i))) := by
    intro i
    let p₆ := firstPair 4
    have h := (hall _ _ (pair_distinct p₆) _ (dictionary_member i)).reindex (pairRemaining p₆).symm
    rw [←cardMap_eq_contractPair] at h
    apply cone_of_matching
    have he : cardMap p₆ q=actualMap q := by
      apply LinearMap.ext
      intro K
      funext x
      change (∑a : Bool,∑b : Bool,K a b*q (pairInsert (firstPair 4) a b x))=_
      simp only [pairInsert_firstPair]
      rfl
    rwa [he] at h
  have cards : ∀i : Fin 12,actualMap q (dictionary (representative .tetrahedral i))=0 ∨
      Nonempty (NonsingularCard (actualMap q (dictionary (representative .tetrahedral i)))) := by
    intro i
    rcases cones i with hz | ⟨r,U,V,hU,hV,he⟩
    · exact Or.inl hz
    · rw [he]
      exact Or.inr ⟨Holant.Platonic.RankDeficientLocalization.Normalization.fourCard r U V
        hU.det_ne_zero hV.det_ne_zero⟩
  have hm := localized_mixed p f R L q (closureScale L C) hs h₀ h₁
  obtain ⟨R₆⟩ := platonic_mixed_rainbow .tetrahedral dictionary (actualMap q) cards hm
  exact GlobalCloseCompletionOctahedralExternalNoRainbow.no_rainbow (actualMap q) _ cones R₆

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalLocalization
end
