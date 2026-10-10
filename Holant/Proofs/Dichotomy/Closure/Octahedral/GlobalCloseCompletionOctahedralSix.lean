import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralSixGeometry
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicSixCards
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixRank

/-! A literal O six-port tensor with its complete matching deck factors.
The unrestricted rainbow classification yields30 maps; every one is rejected
by an explicit original-pair contraction. No six-port classifier is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralSix
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.RankDeficientLocalization
open Holant.Platonic.RankDeficientLocalization.Normalization (DomainAction matchingCone_card)
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Platonic.TetrahedralLocalization
open Holant.Platonic.StabilizerShortening Holant.Platonic.StabilizerLine
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Pauli.ExoticKlein.Fiber
open GlobalCloseCompletionTetrahedralSix.Normalization
open GlobalCloseCompletionPlatonicSix
namespace R
export GlobalCloseCompletionTetrahedralSix.Rank
  (actualMap_injective currentRank rank_zero_iff rank_one_factor)
end R
namespace O
export Holant.Certificates.PlatonicBridgeInterface.Octahedral
  (sourceMap sourceMap_contract normalized_iff_source normalized_iff)
end O
namespace C
export GlobalCloseCompletionOctahedralSixGeometry
  (low_map_eq regularCard_not_matching full_first_card firstKernel_mem)
end C

theorem physical_actualMap (f : Signature ℂ 6) :
    Holant.Platonic.RainbowLocalization.Physical.cardMap (firstPair 4) f=actualMap f := by
  apply LinearMap.ext
  intro K
  funext x
  change (∑ a : Bool, ∑ b : Bool,K a b*f (pairInsert (firstPair 4) a b x))=_
  simp only [pairInsert_firstPair]
  rfl

theorem no_rainbow (f : Signature ℂ 6) (hp : AllPairs .octahedral f)
    (rainbow : RainbowDomainLine (actualMap f) (representative .octahedral)) : False := by
  obtain ⟨D,L,hL,hn,_⟩ := source_normalization (actualMap f) rainbow hp.prepared
  have hn' := (O.normalized_iff_source (dressedMap D L (actualMap f))).mpr hn
  obtain ⟨i,hi⟩ := (O.normalized_iff _).mp hn'
  let h := (SixDressing.ofDomain D L).tensor f
  have hh : actualMap h=O.sourceMap i := by
    dsimp only [h]
    rw [ofDomain_actualMap,hi]
  have hd : AllPairs .octahedral h := hp.dressing (SixDressing.ofDomain D L)
    (ofDomain_legs_mem D L hL)
  have cases_i : (∃j : Fin 6,i=j.castAdd 24) ∨ (∃j : Fin 24,i=j.natAdd 6) := by
    exact Fin.addCases (motive:=fun k=>(∃j : Fin 6,k=j.castAdd 24) ∨ (∃j : Fin 24,k=j.natAdd 6))
      (fun j=>Or.inl ⟨j,rfl⟩) (fun j=>Or.inr ⟨j,rfl⟩) i
  rcases cases_i with ⟨j,rfl⟩ | ⟨j,rfl⟩
  · rw [C.low_map_eq] at hh
    have he : h=GlobalCloseCompletionTetrahedralSix.normalizedParent (j.castAdd 6) := by
      apply R.actualMap_injective
      rw [hh]
      apply LinearMap.ext
      intro K
      exact TetrahedralBridge.sourceMap_contract _ K
    have hc := hd TetrahedralOrientation.contractOrder Q0
      (quaternion_axis_direction .octahedral 0)
    rw [he] at hc
    have hb : GlobalCloseCompletionTetrahedralSix.badIndex (j.castAdd 3)=j.castAdd 6 := by
      fin_cases j <;> rfl
    apply GlobalCloseCompletionTetrahedralSix.bad_not_matching .octahedral (j.castAdd 3)
    simpa only [GlobalCloseCompletionTetrahedralSix.badCard,hb] using hc
  · have hc := hd (Equiv.refl _) (Q0+Q1) C.firstKernel_mem
    simp only [Tensor.reindex_refl] at hc
    change matchingCone .octahedral (actualMap h (Q0+Q1)) at hc
    rw [hh,C.full_first_card] at hc
    exact C.regularCard_not_matching .octahedral _ hc

theorem factor_or_zero (f : Signature ℂ 6) (hp : AllPairs .octahedral f) :
    f=0 ∨ HasProperTensorFactor f := by
  classical
  by_cases h0 : R.currentRank f=0
  · exact Or.inl ((R.rank_zero_iff f).mp h0)
  right
  by_cases h1 : R.currentRank f=1
  · exact R.rank_one_factor f h1
  have hr : 2≤R.currentRank f := by omega
  have hf : f≠0 := fun h=>h0 ((R.rank_zero_iff f).mpr h)
  rcases platonic_ruling_or_rainbow .octahedral (LinearEquiv.refl ℂ Mat)
    (actualMap f) hr (fun i=>matchingCone_card .octahedral _ (hp.prepared i)) with hm | hR
  · apply common_matching_proper_factor .octahedral (LinearEquiv.refl ℂ Mat)
      (firstPair 4) f hf (by decide)
    · rwa [physical_actualMap]
    · intro i
      rw [physical_actualMap]
      exact matchingCone_card .octahedral _ (hp.prepared i)
    · rwa [physical_actualMap]
  · obtain ⟨rainbow⟩ := hR
    exact False.elim (no_rainbow f hp rainbow)

theorem no_prime (f : Signature ℂ 6) (hp : AllPairs .octahedral f)
    (prime : Prime (⟨6,f⟩ : AnySignature ℂ)) : False := by
  rcases factor_or_zero f hp with hz | factor
  · exact prime.1 hz
  · obtain ⟨a,b,ha,hb,p,u,v,_,_,he⟩ := factor
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


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralSix
end
