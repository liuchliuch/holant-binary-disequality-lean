import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicCardReindex
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixDressing
import Holant.Platonic.RainbowLocalization.PhysicalPorts
import Holant.Platonic.TetrahedralLocalization.Reconstruction

/-! The selected rainbow cards in the exact localization graph remain
matching-distinct after their four surviving original ports are enumerated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicLocalizationCards
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.RainbowOrbit
open Holant.Platonic.RankDeficientLocalization
open Holant.Platonic.RainbowLocalization Holant.Platonic.RainbowLocalization.Physical
open Holant.Platonic.RainbowLocalization.MatchingCut
open Holant.Platonic.TetrahedralLocalization Holant.Platonic.StabilizerShortening
open GlobalCloseCompletionTetrahedralSix.Normalization
open GlobalCloseCompletionPlatonicCardReindex

variable {P : Type*} [Fintype P] [DecidableEq P]
variable {D₀ D₁ D₂ : Presentation ℂ P}

theorem exceptional_matching_ne (L : AlgebraicLocalization D₀ D₁ D₂) :
    (presentationMatching L.exceptional₀).mate≠(presentationMatching L.exceptional₁).mate := by
  have hn : Nonempty (Side (cut L.ports) true) := Fintype.card_pos_iff.mp (by
    rw [side_cut_card,L.card_ports]; decide)
  obtain ⟨p⟩ := hn
  have hp : p.val∈L.ports := (cut_true L.ports p.val).mp p.property
  intro he
  have hh := congrArg (fun m : Equiv.Perm (Side (cut L.ports) true) => (m p).val) he
  rw [L.exceptional₀_mate,L.exceptional₁_mate] at hh
  exact ((L.support p.val).mp hp) hh

def residualEquiv (L : AlgebraicLocalization D₀ D₁ D₂) : Side (cut L.ports) true ≃ Fin 4 :=
  Fintype.equivFinOfCardEq ((side_cut_card L.ports).trans L.card_ports)

theorem sixPortOrder_eq (L : AlgebraicLocalization D₀ D₁ D₂) :
    sixPortOrder L=(Equiv.sumCongr (Equiv.refl Bool) (residualEquiv L)).trans (firstPair 4) := by
  ext j
  cases j with
  | inl b => cases b <;> rfl
  | inr p =>
      change 2+(residualEquiv L p).val=((residualEquiv L p).val+1)+1
      omega

theorem actualMap_reindex (L : AlgebraicLocalization D₀ D₁ D₂) (q : Signature ℂ 6) (K : Matrix Bool Bool ℂ) :
    actualMap q K=Tensor.reindex (residualEquiv L) (cardMap (sixPortOrder L) q K) := by
  rw [sixPortOrder_eq]
  ext x
  have hw (a b : Bool) : pairAssignment
      ((Equiv.sumCongr (Equiv.refl Bool) (residualEquiv L)).trans (firstPair 4))
      a b (fun j => x (residualEquiv L j))=Fin.cons a (Fin.cons b x) := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      cases i using Fin.cases with
      | zero => rfl
      | succ j => simp [pairAssignment,firstPair]
  simp only [actualMap_apply,Signature.contract,Tensor.reindex,cardMap,LinearMap.coe_mk,AddHom.coe_mk,hw]

theorem localized_mixed {n : ℕ} (g : PlatonicModel) (p : Bool ⊕ P≃Fin n) (f : Signature ℂ n)
    (R : RainbowDomainLine (cardMap p f) (representative g))
    (L : AlgebraicLocalization R.card₀.presentation R.card₁.presentation R.card₂.presentation)
    (q : Signature ℂ 6) (c : ℂ) (hc : c≠0)
    (h₀ : cardMap (sixPortOrder L) q (representative g R.first)=c • L.exceptional₀.tensor)
    (h₁ : cardMap (sixPortOrder L) q (representative g R.second)=c • L.exceptional₁.tensor) :
    MixedCards (actualMap q) (representative g) := by
  let e := residualEquiv L
  have he₀ : actualMap q (representative g R.first)=c • Tensor.reindex e L.exceptional₀.tensor := by
    rw [actualMap_reindex L,h₀]
    rfl
  have he₁ : actualMap q (representative g R.second)=c • Tensor.reindex e L.exceptional₁.tensor := by
    rw [actualMap_reindex L,h₁]
    rfl
  let E₀ := cardOfScaledReindex L.exceptional₀ e c hc L.exceptional₀_det L.exceptional₀_scalar _ he₀
  let E₁ := cardOfScaledReindex L.exceptional₁ e c hc L.exceptional₁_det L.exceptional₁_scalar _ he₁
  refine ⟨R.first,R.second,E₀,E₁,?_⟩
  exact scaled_matching_ne L.exceptional₀ L.exceptional₁ e c hc
    L.exceptional₀_det L.exceptional₁_det L.exceptional₀_scalar L.exceptional₁_scalar _ _ he₀ he₁
    (exceptional_matching_ne L)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicLocalizationCards
end
