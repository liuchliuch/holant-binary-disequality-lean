import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixCards
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixRank
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixMinors
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixAffine

/-! Six-port T closure from every actual ordered pair card. The unrestricted
bridge theorem produces twelve maps; nine fail an explicit current card,
and the remaining three have literal affine certificates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.RankDeficientLocalization
open Holant.Platonic.RankDeficientLocalization.Normalization (DomainAction matchingCone_card)
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Platonic.TetrahedralLocalization
open Holant.Platonic.StabilizerShortening Holant.Platonic.StabilizerLine
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Pauli.ExoticKlein.Fiber
open Normalization

theorem AllPairs.prepared {f : Signature ℂ 6} (hf : AllPairs f) :
    ∀ i : Fin 12, matchingCone .tetrahedral (actualMap f (representative .tetrahedral i)) := by
  intro i
  simpa only [Tensor.reindex_refl,actualMap_apply] using hf (Equiv.refl _) _ (representative_mem .tetrahedral i)

theorem physical_actualMap (f : Signature ℂ 6) :
    Holant.Platonic.RainbowLocalization.Physical.cardMap (firstPair 4) f=actualMap f := by
  apply LinearMap.ext
  intro K
  funext x
  change (∑ a : Bool, ∑ b : Bool, K a b*f (pairInsert (firstPair 4) a b x))=_
  simp only [pairInsert_firstPair]
  rfl

theorem fixed_factor (f : Signature ℂ 6) (hf : f≠0) (hp : AllPairs f)
    (hr : 2≤Rank.currentRank f)
    (hm : CommonMatching (actualMap f) .tetrahedral (LinearEquiv.refl ℂ Mat)) :
    HasProperTensorFactor f := by
  apply common_matching_proper_factor .tetrahedral (LinearEquiv.refl ℂ Mat)
    (firstPair 4) f hf (by decide)
  · rwa [physical_actualMap]
  · intro i
    rw [physical_actualMap]
    exact matchingCone_card .tetrahedral _ (hp.prepared i)
  · rwa [physical_actualMap]

theorem normalized_preserving (f : Signature ℂ 6) (hp : AllPairs f)
    (R : RainbowDomainLine (actualMap f) (representative .tetrahedral)) :
    ∃ D : DomainAction .tetrahedral, ∃ L : Legs, ∃ hL : GroupLegs .tetrahedral L,
      ∃ s : Fin 3, (SixDressing.ofDomain D L).tensor f=TetrahedralAffine.complexAncestor s := by
  obtain ⟨D,L,hL,hn,_⟩ := source_normalization (actualMap f) R hp.prepared
  have hn' := (TetrahedralBridge.normalized_iff_source (dressedMap D L (actualMap f))).mpr hn
  obtain ⟨i,hi⟩ := (TetrahedralBridge.normalized_iff _).mp hn'
  have he : (SixDressing.ofDomain D L).tensor f=normalizedParent i := by
    apply Rank.actualMap_injective
    rw [ofDomain_actualMap,hi]
    apply LinearMap.ext
    intro K
    exact TetrahedralBridge.sourceMap_contract i K
  have hd := hp.dressing (SixDressing.ofDomain D L) (ofDomain_legs_mem D L hL)
  rcases source_indices i with ⟨b,rfl⟩ | ⟨s,rfl⟩
  · have hc := hd TetrahedralOrientation.contractOrder Q0 (quaternion_axis_direction .tetrahedral 0)
    rw [he] at hc
    exact False.elim (bad_not_matching .tetrahedral b hc)
  · refine ⟨D,L,hL,s,?_⟩
    exact he.trans (preserving_parent s)

theorem preserving_affine (D : DomainAction .tetrahedral) (L : Legs)
    (hL : GroupLegs .tetrahedral L) (f : Signature ℂ 6) (s : Fin 3)
    (he : (SixDressing.ofDomain D L).tensor f=TetrahedralAffine.complexAncestor s) :
    ComplexAffine f := by
  obtain ⟨a,ha,hea⟩ := TetrahedralAffine.source_ancestor_affine s
  have h : ComplexAffine ((SixDressing.ofDomain D L).tensor f) := by
    rw [he]
    exact ⟨1,a,ha,fun x => by simpa only [one_mul] using (hea x).symm⟩
  have hc := (Affine.reindex_iff (SixDressing.ofDomain D L).portOrder
    (Signature.coordinateAction (SixDressing.ofDomain D L).legs f)).mp h
  exact (Affine.coordinate_action_iff (SixDressing.ofDomain D L).legs
    (ofDomain_legs_mem D L hL) f).mp hc

theorem factor_or_affine (f : Signature ℂ 6) (hp : AllPairs f) :
    f=0 ∨ HasProperTensorFactor f ∨ ComplexAffine f := by
  classical
  by_cases h0 : Rank.currentRank f=0
  · exact Or.inl ((Rank.rank_zero_iff f).mp h0)
  right
  by_cases h1 : Rank.currentRank f=1
  · exact Or.inl (Rank.rank_one_factor f h1)
  have hr : 2≤Rank.currentRank f := by omega
  have hf : f≠0 := fun h => h0 ((Rank.rank_zero_iff f).mpr h)
  rcases platonic_ruling_or_rainbow .tetrahedral (LinearEquiv.refl ℂ Mat)
    (actualMap f) hr (fun i => matchingCone_card .tetrahedral _ (hp.prepared i)) with hm | hR
  · exact Or.inl (fixed_factor f hf hp hr hm)
  · obtain ⟨R⟩ := hR
    obtain ⟨D,L,hL,s,he⟩ := normalized_preserving f hp R
    exact Or.inr (preserving_affine D L hL f s he)

theorem prime_affine (f : Signature ℂ 6) (hp : AllPairs f)
    (prime : Prime (⟨6,f⟩ : AnySignature ℂ)) : ComplexAffine f := by
  rcases factor_or_affine f hp with hz | factor | affine
  · exact False.elim (prime.1 hz)
  · obtain ⟨a,b,ha,hb,p,u,v,_,_,he⟩ := factor
    apply False.elim
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
  · exact affine


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix
end
