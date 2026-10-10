import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralSixClassification
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicSixNamedCards
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicLocalizationCards
import Holant.Certificates.PlatonicAtlas.Spanning

/-! A genuine current I rainbow line of any arity localizes to an actual
six-port graph, whose inherited entire I deck contradicts the six-port
coefficient classification. Original closure kernels and scales are kept. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.Higher
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.RainbowOrbit
open Holant.Platonic.RankDeficientLocalization
open Holant.Platonic.RainbowLocalization Holant.Platonic.RainbowLocalization.Physical
open GlobalCloseCompletionPlatonicHigherCards GlobalCloseCompletionPlatonicSix
open GlobalCloseCompletionPlatonicSixNamedCards GlobalCloseCompletionPlatonicLocalizationCards
open GlobalCloseCompletionTetrahedralSix.Normalization

private theorem directions_span : Submodule.span ℂ (directions .icosahedral)=⊤ := by
  apply top_unique
  rw [←PlatonicAtlas.sourceAxes_span]
  apply Submodule.span_mono
  rintro U ⟨i,rfl⟩
  exact PlatonicAtlas.sourceAxes_actual .icosahedral i

/-- Pure coefficient form of the same localization. It asserts no new
physical resource: each selected closure is used only in the exact finite
sum identity needed to contradict the full six-port coefficient deck. -/
theorem no_rainbow_coefficients {n : ℕ} {P : Type*} [Fintype P] [DecidableEq P]
    (p : Bool ⊕ P≃Fin n) (f : Signature ℂ n)
    (hdeck : ∀u v : Fin n,u≠v→∀K,groupDirection .icosahedral K→
      MatchingOrZero (directions .icosahedral) (contractPair u v K f))
    (R : RainbowDomainLine (cardMap p f) (representative .icosahedral)) : False := by
  let G := directions .icosahedral
  have hG := directions_group .icosahedral
  have hX := directions_X .icosahedral
  have hrev := directions_reversal .icosahedral
  have value₀ : cardMap p f (representative .icosahedral R.first)=R.card₀.presentation.tensor :=
    R.card₀.value
  have value₁ : cardMap p f (representative .icosahedral R.second)=R.card₁.presentation.tensor :=
    R.card₁.value
  have value₂ : cardMap p f (representative .icosahedral R.third)=R.card₂.presentation.tensor :=
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
  have h₀ : cardMap (sixPortOrder L) q (representative .icosahedral R.first)=
      closureScale L C • L.exceptional₀.tensor := by
    calc
      _ = contractCollection (localizedPorts L) C
          (cardMap p f (representative .icosahedral R.first)) :=
        cardMap_full_closure p (localizedPorts L) (sixPortOrder L) C f _
      _ = contractCollection (localizedPorts L) C R.card₀.presentation.tensor :=
        congrArg (fun F : Tensor ℂ P => contractCollection (localizedPorts L) C F) value₀
      _ = _ := close_factorized L C _ _ L.factor₀
  have h₁ : cardMap (sixPortOrder L) q (representative .icosahedral R.second)=
      closureScale L C • L.exceptional₁.tensor := by
    calc
      _ = contractCollection (localizedPorts L) C
          (cardMap p f (representative .icosahedral R.second)) :=
        cardMap_full_closure p (localizedPorts L) (sixPortOrder L) C f _
      _ = contractCollection (localizedPorts L) C R.card₁.presentation.tensor :=
        congrArg (fun F : Tensor ℂ P => contractCollection (localizedPorts L) C F) value₁
      _ = _ := close_factorized L C _ _ L.factor₁
  have hc : ∀e,SafeBinary G (C e) := fun e => (directions_safe_iff .icosahedral _).mpr (hC e)
  have hall := all_cards_after_collection G hG hX hrev G (originalClosurePorts L p) C f hc hdeck
  have hp : AllPairs .icosahedral q := all_pairs_of_named .icosahedral q hall
  have hm := localized_mixed .icosahedral p f R L q (closureScale L C) hs h₀ h₁
  obtain ⟨R₆⟩ := platonic_mixed_rainbow .icosahedral (LinearEquiv.refl ℂ Mat)
    (actualMap q) (fun i => Holant.Platonic.RankDeficientLocalization.Normalization.matchingCone_card
      .icosahedral _ (hp.prepared i)) hm
  exact Six.no_mixed_six q hp R₆


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.Higher
end
