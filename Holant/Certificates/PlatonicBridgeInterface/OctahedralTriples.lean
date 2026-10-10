import Holant.Certificates.PlatonicBridgeInterface.OctahedralFiniteData

/-! Exhaustivity for arbitrary complex bridge triples, with no finite-coverage
premise: the twelve-point theorem supplies the reduction to checked rows. -/
namespace Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.IcosahedralSeparator (GScalar gadd gint gembed gembed_add gembed_injective gembed_ne_zero)
noncomputable section
set_option backward.isDefEq.respectTransparency false

def target : FourTensor := fun x => (A x+B x)/2

theorem goodTriple_iff_ordered (t : Fin 3 → Fin 12) :
    GoodTriple t ↔ ∃ i : Fin 30, t = ordered i := by
  have ht : t = ![t 0,t 1,t 2] := by funext j; fin_cases j <;> rfl
  rw [ht]
  generalize t 0 = a, t 1 = b, t 2 = c
  fin_cases a
  · exact goodTriple_first_0 b c
  · exact goodTriple_first_1 b c
  · exact goodTriple_first_2 b c
  · exact goodTriple_first_3 b c
  · exact goodTriple_first_4 b c
  · exact goodTriple_first_5 b c
  · exact goodTriple_first_6 b c
  · exact goodTriple_first_7 b c
  · exact goodTriple_first_8 b c
  · exact goodTriple_first_9 b c
  · exact goodTriple_first_10 b c
  · exact goodTriple_first_11 b c

theorem goodTriple_iff_sum (t : Fin 3 → Fin 12) :
    GoodTriple t ↔ candidate (t 0)+candidate (t 1)+candidate (t 2)=target := by
  have he (x : Fin 4 → Bool) : 8*candidate 1 x+8*candidate 2 x = 8*target x := by
    change 8*((1/2:ℂ)*A x)+8*((1/2:ℂ)*B x)=8*((A x+B x)/2)
    ring
  constructor
  · intro h
    funext x
    obtain ⟨w,rfl⟩ := TetrahedralDeck.words_surjective x
    have hh := congrArg gembed (h w)
    simp only [candidateTable_correct,gembed_add,gembed_candidateCode] at hh
    rw [he] at hh
    change candidate (t 0) (TetrahedralDeck.words w)+candidate (t 1) (TetrahedralDeck.words w)+
      candidate (t 2) (TetrahedralDeck.words w)=target (TetrahedralDeck.words w)
    linear_combination hh/8
  · intro h w
    apply gembed_injective
    simp only [candidateTable_correct,gembed_add,gembed_candidateCode]
    rw [he]
    have hh := congrFun h (TetrahedralDeck.words w)
    change candidate (t 0) (TetrahedralDeck.words w)+candidate (t 1) (TetrahedralDeck.words w)+
      candidate (t 2) (TetrahedralDeck.words w)=target (TetrahedralDeck.words w) at hh
    linear_combination 8*hh

def orderedTuple (i : Fin 30) : Fin 3 → FourTensor := fun j => candidate (ordered i j)

theorem orderedTuple_injective : Function.Injective orderedTuple := by
  intro i j h
  apply ordered_injective
  funext k
  apply candidate_injective
  exact congrFun h k

theorem triple_iff (W : Fin 3 → FourTensor) :
    ((∀ j, bridgeConditions .octahedral (W j)) ∧ W 0+W 1+W 2=target) ↔
      ∃ i : Fin 30, W = orderedTuple i := by
  classical
  constructor
  · rintro ⟨hW,hS⟩
    choose t ht using fun j => (bridge_iff (W j)).mp (hW j)
    have hg : GoodTriple t := (goodTriple_iff_sum t).mpr (by simpa only [←ht] using hS)
    obtain ⟨i,hi⟩ := (goodTriple_iff_ordered t).mp hg
    refine ⟨i,?_⟩
    funext j
    rw [ht j,hi]
    rfl
  · rintro ⟨i,rfl⟩
    exact ⟨fun j => candidate_bridge _,(goodTriple_iff_sum _).mp (ordered_valid i)⟩

def solutionTriples : Finset (Fin 3 → FourTensor) := by
  classical
  exact Finset.univ.image orderedTuple

theorem solutionTriples_card : solutionTriples.card = 30 := by
  classical
  rw [solutionTriples,Finset.card_image_of_injective _ orderedTuple_injective]
  simp

theorem high_orderedTuple (i : Fin 24) (j : Fin 3) :
    orderedTuple (i.natAdd 6) j = regular (ordering i j) := by
  simp [orderedTuple,ordered,candidate]

theorem low_orderedTuple (i : Fin 6) (j : Fin 3) :
    orderedTuple (i.castAdd 24) j = ![0,(1/2 : ℂ) • A,(1/2 : ℂ) • B] (permutation i j) := by
  simp [orderedTuple,ordered,candidate]

end
end Holant.Certificates.PlatonicBridgeInterface.Octahedral
