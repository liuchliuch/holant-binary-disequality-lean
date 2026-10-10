import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralExternalLocalization
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicHigherRank

/-! Full external-T all-arity coefficient exclusion. Every hypothesis is
an actual named pair-card value; rank and matching alternatives and the
localized six-port contradiction are derived internally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalCoefficients
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.RainbowOrbit
open Holant.Platonic.RankDeficientLocalization
open Holant.Platonic.RainbowLocalization.Physical Holant.Platonic.TetrahedralLocalization
open Holant.Pauli.ExoticKlein.Fiber
open Holant.LocalDrafts.FinitePGL2.Stabilization
open GlobalCloseCompletionOctahedralExternalDeck

theorem factor_or_zero {m : ℕ} (f : Signature ℂ (m+2)) (hm : 6≤m+2)
    (hdeck : ∀u v : Fin (m+2),u≠v→∀K,RainbowOrbit.External.Direction K→
      MatchingOrZero directions (contractPair u v K f)) :
    f=0 ∨ HasProperTensorFactor f := by
  classical
  by_cases h0 : GlobalCloseCompletionPlatonicHigherRank.currentRank f=0
  · exact Or.inl ((GlobalCloseCompletionPlatonicHigherRank.rank_zero_iff f).mp h0)
  right
  by_cases h1 : GlobalCloseCompletionPlatonicHigherRank.currentRank f=1
  · exact GlobalCloseCompletionPlatonicHigherRank.rank_one_factor f (by omega) h1
  have hr : 2≤GlobalCloseCompletionPlatonicHigherRank.currentRank f := by omega
  have hf : f≠0 := fun h => h0 ((GlobalCloseCompletionPlatonicHigherRank.rank_zero_iff f).mpr h)
  let p := firstPair m
  have hcards : ∀i : Fin 12,cardMap p f (dictionary (representative .tetrahedral i))=0 ∨
      Nonempty (NonsingularCard (cardMap p f (dictionary (representative .tetrahedral i)))) := by
    intro i
    have h := (hdeck _ _ (pair_distinct p) _ (dictionary_member i)).reindex
      (pairRemaining p).symm
    rw [←cardMap_eq_contractPair] at h
    rcases h with hz | ⟨M,hM,hc,he⟩
    · exact Or.inl hz
    · exact Or.inr ⟨⟨M,fun j => SafeBinary.nonsingular directions_group (hM j),hc,he⟩⟩
  change 2≤Module.finrank ℂ (cardMap p f).range at hr
  rcases platonic_ruling_or_rainbow .tetrahedral dictionary
    (cardMap p f) hr hcards with common | rainbow
  · exact common_matching_proper_factor .tetrahedral dictionary p f hf hm hr hcards common
  · obtain ⟨R⟩ := rainbow
    exact (GlobalCloseCompletionOctahedralExternalLocalization.no_rainbow_coefficients p f hdeck R).elim

theorem prime_no_factor {n : ℕ} (f : Signature ℂ n)
    (prime : Prime (⟨n,f⟩ : AnySignature ℂ)) : ¬HasProperTensorFactor f := by
  rintro ⟨a,b,ha,hb,p,u,v,_,_,he⟩
  apply prime.2
  exact ⟨⟨a,u⟩,⟨b,v⟩,⟨{
    left_pos:=ha
    right_pos:=hb
    ports:=p
    scale:=1
    equation:=by
      funext x
      change f x=(1 : ℂ)*(u (fun i=>x (p (.inl i)))*v (fun i=>x (p (.inr i))))
      simpa only [Tensor.reindex,Tensor.tensor,one_mul] using congrFun he x }⟩⟩

theorem prime_impossible {m : ℕ} (f : Signature ℂ (m+2)) (hm : 6≤m+2)
    (hdeck : ∀u v : Fin (m+2),u≠v→∀K,RainbowOrbit.External.Direction K→
      MatchingOrZero directions (contractPair u v K f))
    (prime : Prime (⟨m+2,f⟩ : AnySignature ℂ)) : False := by
  rcases factor_or_zero f hm hdeck with hz | hf
  · exact prime.1 hz
  · exact prime_no_factor f prime hf


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalCoefficients
end
