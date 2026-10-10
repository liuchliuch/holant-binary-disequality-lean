import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicSixCards
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixRank
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixMinors
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralUniformRanks
import Holant.Certificates.IcosahedralSeparator.Maps

/-! Standard I six-port classification from the entire actual pair deck.
The exhaustive 36-map normalization is contradicted by actual group-kernel
cards: six low maps use the original ports 1/3, and all thirty high maps use
the same original first pair and the literal uniform I kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.Six
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.RankDeficientLocalization
open Holant.Platonic.RankDeficientLocalization.Normalization (DomainAction matchingCone_card)
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Platonic.TetrahedralLocalization
open Holant.Platonic.StabilizerShortening
open Holant.Pauli.ExoticKlein.Fiber
open Holant.LocalDrafts.FinitePGL2.Stabilization
open GlobalCloseCompletionTetrahedralSix.Normalization
open GlobalCloseCompletionPlatonicSix

theorem rank_three_not_matching (g : PlatonicModel) (q : FourTensor)
    (hq : ∀r : Fin 3,(flatten r q).rank=3) : ¬matchingCone g q := by
  intro hm
  rcases matchingCone_presentation g q hm with rfl | ⟨r,U,V,hU,hV,rfl⟩
  · have h := hq 0
    norm_num at h
  · have h := hq r
    rw [matching_flattening_rank r r U V (groupDirection_det_ne_zero g hU)
      (groupDirection_det_ne_zero g hV),if_pos rfl] at h
    omega

private theorem low_map_eq (i : Fin 6) :
    IcosahedralSeparator.sourceMap (i.castAdd 30)=TetrahedralBridge.sourceMap (i.castAdd 6) := by
  apply TetrahedralBridge.map_ext_basis
  intro k
  rw [IcosahedralSeparator.sourceMap_basis,TetrahedralBridge.sourceMap_basis]
  fin_cases i <;> fin_cases k <;> rfl

private theorem uniform_output_map (i : Fin 30) :
    IcosahedralSeparator.sourceMap (i.natAdd 6) IcosahedralSeparator.uniformKernel=
      IcosahedralSeparator.uniformOutput i := by
  simp only [IcosahedralSeparator.uniformKernel,map_add,map_sub,map_smul,
    IcosahedralSeparator.uniformOutput]
  change (goldenRatio : ℂ) • IcosahedralSeparator.sourceMap (i.natAdd 6)
      (quaternionBasis (0 : Fin 3).succ) -
    (goldenReciprocal : ℂ) • IcosahedralSeparator.sourceMap (i.natAdd 6)
      (quaternionBasis (1 : Fin 3).succ) +
    IcosahedralSeparator.sourceMap (i.natAdd 6) (quaternionBasis (2 : Fin 3).succ)=_
  simp only [IcosahedralSeparator.sourceMap_next,IcosahedralSeparator.high_orderedTuple]

theorem no_mixed_six (f : Signature ℂ 6) (hp : AllPairs .icosahedral f)
    (R : RainbowDomainLine (actualMap f) (representative .icosahedral)) : False := by
  obtain ⟨D,L,hL,hn,_⟩ := source_normalization (actualMap f) R hp.prepared
  have hn' := (IcosahedralSeparator.normalized_iff_source (dressedMap D L (actualMap f))).mpr hn
  obtain ⟨i,hi⟩ := (IcosahedralSeparator.normalized_iff _).mp hn'
  have hd := hp.dressing (SixDressing.ofDomain D L) (ofDomain_legs_mem D L hL)
  revert hi
  refine Fin.addCases (m:=6) (n:=30) (fun b hi => ?_) (fun b hi => ?_) i
  · have he : (SixDressing.ofDomain D L).tensor f=GlobalCloseCompletionTetrahedralSix.normalizedParent (b.castAdd 6) := by
      apply GlobalCloseCompletionTetrahedralSix.Rank.actualMap_injective
      rw [ofDomain_actualMap,hi,low_map_eq]
      apply LinearMap.ext
      intro K
      exact TetrahedralBridge.sourceMap_contract (b.castAdd 6) K
    have hc := hd TetrahedralOrientation.contractOrder Q0 (quaternion_axis_direction .icosahedral 0)
    rw [he] at hc
    have hb : GlobalCloseCompletionTetrahedralSix.badIndex (b.castAdd 3)=b.castAdd 6 := by fin_cases b <;> rfl
    exact GlobalCloseCompletionTetrahedralSix.bad_not_matching .icosahedral (b.castAdd 3) (by simpa only [GlobalCloseCompletionTetrahedralSix.badCard,hb] using hc)
  · have hc := dressedMap_cards D L hL (actualMap f)
      (cards_of_representatives .icosahedral _ hp.prepared) IcosahedralSeparator.uniformKernel IcosahedralSeparator.uniformKernel_group
    rw [hi] at hc
    change matchingCone .icosahedral
      (IcosahedralSeparator.sourceMap (b.natAdd 6) IcosahedralSeparator.uniformKernel) at hc
    rw [uniform_output_map] at hc
    exact rank_three_not_matching .icosahedral _ (UniformRanks.output_ranks b) hc

private theorem physical_actualMap (f : Signature ℂ 6) :
    Holant.Platonic.RainbowLocalization.Physical.cardMap (firstPair 4) f=actualMap f := by
  apply LinearMap.ext
  intro K
  funext x
  change (∑ a : Bool, ∑ b : Bool, K a b*f (pairInsert (firstPair 4) a b x))=_
  simp only [pairInsert_firstPair]
  rfl

theorem factor_or_zero (f : Signature ℂ 6) (hp : AllPairs .icosahedral f) :
    f=0 ∨ HasProperTensorFactor f := by
  classical
  by_cases h0 : GlobalCloseCompletionTetrahedralSix.Rank.currentRank f=0
  · exact Or.inl ((GlobalCloseCompletionTetrahedralSix.Rank.rank_zero_iff f).mp h0)
  right
  by_cases h1 : GlobalCloseCompletionTetrahedralSix.Rank.currentRank f=1
  · exact GlobalCloseCompletionTetrahedralSix.Rank.rank_one_factor f h1
  have hr : 2≤GlobalCloseCompletionTetrahedralSix.Rank.currentRank f := by omega
  have hf : f≠0 := fun h => h0 ((GlobalCloseCompletionTetrahedralSix.Rank.rank_zero_iff f).mpr h)
  rcases platonic_ruling_or_rainbow .icosahedral (LinearEquiv.refl ℂ Mat)
    (actualMap f) hr (fun i => matchingCone_card .icosahedral _ (hp.prepared i)) with hm | hR
  · apply common_matching_proper_factor .icosahedral (LinearEquiv.refl ℂ Mat)
      (firstPair 4) f hf (by decide)
    · rwa [physical_actualMap]
    · intro i
      rw [physical_actualMap]
      exact matchingCone_card .icosahedral _ (hp.prepared i)
    · rwa [physical_actualMap]
  · obtain ⟨R⟩ := hR
    exact (no_mixed_six f hp R).elim

theorem prime_impossible (f : Signature ℂ 6) (hp : AllPairs .icosahedral f)
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


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.Six
end
