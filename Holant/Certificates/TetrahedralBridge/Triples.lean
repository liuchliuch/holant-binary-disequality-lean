import Holant.Certificates.TetrahedralBridge.Bridge
import Holant.Certificates.TetrahedralBridge.FiniteData
import Holant.Certificates.TetrahedralDeck.CardSemantics

/-! The finite sum check is transported to actual complex bridge vectors.
Completeness begins with the proved unrestricted six-point cone theorem. -/
namespace Holant.Certificates.TetrahedralBridge
open Holant Holant.Certificates.TwelveLoops Holant.Certificates.TetrahedralDeck
open Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem actualKernel_axis (k : Fin 4) : actualKernel (k.castAdd 8) = quaternionBasis k := by
  simp [actualKernel,representative,TetrahedralAffine.complexKernel]

theorem embed_gCandidate (i : Fin 6) (x : Word) : embed (gCandidate i x) = 2*candidate i x := by
  have h0 : actualKernel 0 = Q0 := actualKernel_axis 0
  have h1 : actualKernel 1 = Q1 := actualKernel_axis 1
  have h3 : actualKernel 3 = Q3 := actualKernel_axis 3
  have hz : embed gzero = 0 := by norm_num [embed,gzero]
  fin_cases i <;>
    norm_num [gCandidate,embed_gMatch,embed_gneg,h0,h1,h3,hz,candidate,regular,axisIndex,
      TetrahedralOrientation.axisR,matchingProduct,A,B,P0,P1,P2,smul_eq_mul] <;> ring

theorem embed_injective : Function.Injective embed := by
  intro a b h
  apply Prod.ext
  · have he : (a.1 : ℝ) = (b.1 : ℝ) := by simpa [embed] using congrArg Complex.re h
    exact_mod_cast he
  · have he : (a.2 : ℝ) = (b.2 : ℝ) := by simpa [embed] using congrArg Complex.im h
    exact_mod_cast he

theorem candidate_injective : Function.Injective candidate := by
  intro i j h
  apply candidateCode_injective
  funext w
  apply embed_injective
  change embed (gCandidate i (words w)) = embed (gCandidate j (words w))
  rw [embed_gCandidate,embed_gCandidate,h]

def target : FourTensor := fun x => (A x+B x)/2

theorem twice_target (x : Word) : 2*target x = 2*candidate 1 x + 2*candidate 2 x := by
  simp [target,candidate,smul_eq_mul]
  ring

theorem goodTriple_iff_sum (t : Fin 3 → Fin 6) :
    GoodTriple t ↔ candidate (t 0)+candidate (t 1)+candidate (t 2)=target := by
  constructor
  · intro h
    funext x
    obtain ⟨j,rfl⟩ := words_surjective x
    have he := congrArg embed (h j)
    simp only [candidateCode,embed_add,embed_gCandidate] at he
    rw [← twice_target] at he
    change candidate (t 0) (words j)+candidate (t 1) (words j)+candidate (t 2) (words j)=target (words j)
    linear_combination he/2
  · intro h j
    apply embed_injective
    simp only [candidateCode,embed_add,embed_gCandidate]
    rw [← twice_target]
    have he := congrFun h (words j)
    change candidate (t 0) (words j)+candidate (t 1) (words j)+candidate (t 2) (words j)=target (words j) at he
    linear_combination 2*he

def orderedTuple (i : Fin 12) : Fin 3 → FourTensor := fun j => candidate (ordered i j)

theorem orderedTuple_injective : Function.Injective orderedTuple := by
  intro i j h
  apply ordered_injective
  funext k
  apply candidate_injective
  exact congrFun h k

/-- Every simultaneous-cone solution of the source sum equation occurs once in
the twelve ordered triples; the starting tensors are arbitrary complex functions. -/
theorem triple_iff (W : Fin 3 → FourTensor) :
    ((∀ j, bridgeConditions .tetrahedral (W j)) ∧ W 0+W 1+W 2=target) ↔
      ∃ i : Fin 12, W = orderedTuple i := by
  classical
  constructor
  · rintro ⟨hW,hS⟩
    choose t ht using fun j => (bridge_iff (W j)).mp (hW j)
    have hg : GoodTriple t := (goodTriple_iff_sum t).mpr (by simpa only [← ht] using hS)
    obtain ⟨i,hi⟩ := (goodTriple_iff_ordered t).mp hg
    refine ⟨i,?_⟩
    funext j
    rw [ht j,hi]
    rfl
  · rintro ⟨i,rfl⟩
    exact ⟨fun j => candidate_bridge _,(goodTriple_iff_sum _).mp
      ((goodTriple_iff_ordered _).mpr ⟨i,rfl⟩)⟩

noncomputable def solutionTriples : Finset (Fin 3 → FourTensor) := by
  classical
  exact Finset.univ.image orderedTuple

theorem solutionTriples_card : solutionTriples.card = 12 := by
  classical
  rw [solutionTriples,Finset.card_image_of_injective _ orderedTuple_injective]
  simp

end
end Holant.Certificates.TetrahedralBridge
