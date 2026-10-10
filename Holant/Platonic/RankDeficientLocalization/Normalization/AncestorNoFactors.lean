import Holant.Platonic.RankDeficientLocalization.Normalization.CutTransport
import Holant.Platonic.RankDeficientLocalization.Normalization.MarkedAssembly
import Holant.Certificates.PlatonicDeficient.AncestorPairData
import Holant.OpenNetworkComposition.FactorFreeNormalization.PairRanks

/-! The normalized ancestors have no binary factor at any original pair.
This obstruction is transported back through the actual six-port normalization
and removes the retained-I condition from their ordinary-gadget conversion. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.RainbowLocalization
open Holant.Platonic.RainbowLocalization.MatchingCut (Side joinAssignment)
open Holant.OpenNetworkComposition.FactorFreeNormalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical

namespace Ancestor
open PlatonicDeficient

theorem join_restrictions (i j : Fin 6) (x y : Fin 6 → Bool) :
    joinAssignment (Cut.pairCut i j) (fun p : Side (Cut.pairCut i j) true => x p.val)
      (fun p : Side (Cut.pairCut i j) false => y p.val)=spliceWord i j x y := by
  funext k
  by_cases hk : k=i ∨ k=j <;> simp [joinAssignment,Cut.pairCut,spliceWord,hk]

def minorRows (p : Fin 6) (t : Fin 15) :
    Fin 2 → (Side (Cut.pairCut (TetrahedralDeck.pairs t).1 (TetrahedralDeck.pairs t).2) true → Bool) :=
  fun r k => sixWord (ancestorMinorWords p t (r.castAdd 2)) k.val

def minorColumns (p : Fin 6) (t : Fin 15) :
    Fin 2 → (Side (Cut.pairCut (TetrahedralDeck.pairs t).1 (TetrahedralDeck.pairs t).2) false → Bool) :=
  fun r k => sixWord (ancestorMinorWords p t (r.natAdd 2)) k.val

theorem actual_minor (p : Fin 6) (t : Fin 15) :
    ((MatchingCut.flatten (Cut.pairCut (TetrahedralDeck.pairs t).1 (TetrahedralDeck.pairs t).2)
      (ancestor p)).submatrix (minorRows p t) (minorColumns p t)).det=
        OctahedralSeparator.embed (ancestorPairMinor p t) := by
  have hj (a b : Fin 2) :
      joinAssignment (Cut.pairCut (TetrahedralDeck.pairs t).1 (TetrahedralDeck.pairs t).2)
        (minorRows p t a) (minorColumns p t b)=
      spliceWord (TetrahedralDeck.pairs t).1 (TetrahedralDeck.pairs t).2
        (sixWord (ancestorMinorWords p t (a.castAdd 2)))
        (sixWord (ancestorMinorWords p t (b.natAdd 2))) :=
    join_restrictions _ _ _ _
  rw [Matrix.det_fin_two]
  change ancestor p (joinAssignment _ (minorRows p t 0) (minorColumns p t 0))*
      ancestor p (joinAssignment _ (minorRows p t 1) (minorColumns p t 1))-
      ancestor p (joinAssignment _ (minorRows p t 0) (minorColumns p t 1))*
      ancestor p (joinAssignment _ (minorRows p t 1) (minorColumns p t 0))=_
  rw [hj,hj,hj,hj]
  unfold ancestorPairMinor
  rw [OctahedralSeparator.embed_sub,OctahedralSeparator.embed_mul,OctahedralSeparator.embed_mul]
  rfl

theorem indexed_pair_rank (p : Fin 6) (t : Fin 15) :
    2≤(MatchingCut.flatten (Cut.pairCut (TetrahedralDeck.pairs t).1 (TetrahedralDeck.pairs t).2)
      (ancestor p)).rank := by
  have hd : ((MatchingCut.flatten (Cut.pairCut (TetrahedralDeck.pairs t).1 (TetrahedralDeck.pairs t).2)
      (ancestor p)).submatrix (minorRows p t) (minorColumns p t)).det≠0 := by
    rw [actual_minor]
    exact OctahedralSeparator.embed_ne_zero (ancestor_pair_minor_nonzero p t)
  have hr := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  have hl := Matrix.rank_submatrix_le
    (MatchingCut.flatten (Cut.pairCut (TetrahedralDeck.pairs t).1 (TetrahedralDeck.pairs t).2) (ancestor p))
    (minorRows p t) (minorColumns p t)
  rw [hr] at hl
  exact hl

theorem all_pair_ranks (p : Fin 6) : Cut.AllPairRanks (ancestor p) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij|hji
  · obtain ⟨t,ht⟩ := (TetrahedralDeck.pairs_complete i j).mp hij
    have hh := indexed_pair_rank p t
    rw [ht] at hh
    exact hh
  · obtain ⟨t,ht⟩ := (TetrahedralDeck.pairs_complete j i).mp hji
    have hh := indexed_pair_rank p t
    rw [ht] at hh
    have he : Cut.pairCut j i=Cut.pairCut i j := by funext k; simp [Cut.pairCut,or_comm]
    rw [he] at hh
    exact hh

theorem marked_all_pair_ranks (f : Form) (p : Fin 6) :
    Cut.AllPairRanks (OctahedralSeparator.complexTensor (OctahedralSeparator.deficientAncestor f p)) := by
  have hd : ∀j : Fin 6,(OctahedralSeparator.complexMatrix (OctahedralSeparator.sixLegs f j)).det≠0 := by
    intro j
    fin_cases j <;>
      simp [OctahedralSeparator.sixLegs,OctahedralSeparator.complexMatrix_mt,
        OctahedralSeparator.complexMatrix_inverseConjugator,Matrix.det_transpose,Matrix.det_nonsing_inv,
        OctahedralSeparator.complexMatrix_conjugator_det_ne_zero]
  rw [OctahedralSeparator.deficientAncestor,OctahedralSeparator.complexTensor_action]
  exact (Cut.allPair_action _ hd _).mpr (all_pair_ranks p)

end Ancestor

theorem standard_ancestor_noXFactor (g : PlatonicModel) (h : Signature ℂ 6)
    (hc : ∀i,matchingCone g (actualMap h (representative g i)))
    (hm : MixedCards (actualMap h) (representative g))
    (hr : Module.finrank ℂ (actualMap h).range<4) : NoXFactor h := by
  obtain ⟨p,D,L,hL,he,_⟩ := standard_deficient_normalization g h hc hm hr
  have hd : ∀j,((SixDressing.ofDomain D L).legs j).det≠0 := fun j =>
    groupDirection_det_ne_zero g (ofDomain_legs_mem D L hL j)
  have hh : Cut.AllPairRanks ((SixDressing.ofDomain D L).tensor h) := he.symm ▸ Ancestor.all_pair_ranks p
  exact noXFactor_of_pairRanks h ((Cut.allPair_sixDressing _ hd h).mp hh)

theorem marked_ancestor_noXFactor (f : Form) (h : Signature ℂ 6)
    (hc : ∀i,MarkedCone f (actualMap h (markedRepresentative f i)))
    (hm : MixedCards (actualMap h) (markedRepresentative f))
    (hr : Module.finrank ℂ (actualMap h).range<4) : NoXFactor h := by
  obtain ⟨p,D,L,hL,he,_⟩ := marked_deficient_normalization f h hc hm hr
  have hd : ∀j,((currentDressing f D L).legs j).det≠0 := fun j =>
    (currentDressing_directions f D L hL j).det_ne_zero
  have hh : Cut.AllPairRanks ((currentDressing f D L).tensor h) :=
    he.symm ▸ Ancestor.marked_all_pair_ranks f p
  exact noXFactor_of_pairRanks h ((Cut.allPair_sixDressing _ hd h).mp hh)

end
end Holant.Platonic.RankDeficientLocalization.Normalization
