import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicNamedCards
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicSixCards

/-! Convert the named-port safe deck of a genuine localized six-port tensor
to the exact literal coefficient predicate used by the finite classifier. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicSixNamedCards
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Platonic.StabilizerShortening Holant.Platonic.TetrahedralLocalization
open GlobalCloseCompletionPlatonicHigherCards GlobalCloseCompletionPlatonicSix

theorem cone_of_matching (g : PlatonicModel) (q : FourTensor)
    (hq : MatchingOrZero (directions g) q) : matchingCone g q := by
  rcases hq with hz | ⟨M,hM,_,rfl⟩
  · exact Or.inl hz
  · apply GlobalCloseCompletionPlatonicMatchingCone.presentation g
    intro e
    exact (directions_safe_iff g _).mp (hM e)

theorem all_pairs_of_named (g : PlatonicModel) (f : Signature ℂ 6)
    (hdeck : ∀u v : Fin 6,u≠v→∀K,groupDirection g K→
      MatchingOrZero (directions g) (contractPair u v K f)) : AllPairs g f := by
  intro order K hK
  let p := (firstPair 4).trans order.symm
  have h := (hdeck _ _ (pair_distinct p) K hK).reindex (pairRemaining p).symm
  rw [←cardMap_eq_contractPair] at h
  apply cone_of_matching g
  have he : cardMap p f K=Signature.contract K (Tensor.reindex order f) :=
    (contract_reindex order K f).symm
  rwa [he] at h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicSixNamedCards
end
