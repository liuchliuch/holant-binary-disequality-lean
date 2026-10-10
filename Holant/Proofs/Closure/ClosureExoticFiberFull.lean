import Holant.Proofs.Closure.ClosureExoticFiberCross

/-! Closed live-row/permutation dichotomy from the actual PairSafe ancestor and
its exact common fibre. No safe-ancestor or full-support backend is assumed. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
noncomputable section
open Holant.Pauli.ExoticKlein
open Holant.Certificates.MatchingContractionClosure
variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

theorem two_other_edges (hr : 3 ≤ r) (d : Fin r) :
    ∃ e f : Fin r, d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  let i : Fin r := ⟨0,by omega⟩
  let j : Fin r := ⟨1,by omega⟩
  let k : Fin r := ⟨2,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [i,j] at this; omega
  have hik : i ≠ k := by intro h; have := congrArg Fin.val h; dsimp [i,k] at this; omega
  have hjk : j ≠ k := by intro h; have := congrArg Fin.val h; dsimp [j,k] at this; omega
  by_cases hi : d = i
  · exact ⟨j,k,hi ▸ hij,hi ▸ hik,hjk⟩
  by_cases hj : d = j
  · exact ⟨i,k,hi,hj ▸ hjk,hik⟩
  exact ⟨i,j,hi,hj,hij⟩

/-- Every tomographic weight is nonzero on the genuine nonfactor branch. -/
theorem all_live (M : Matching P r) (hr : 3 ≤ r)
    (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished : Fin r) (hlabel : ∀ a, labels a distinguished = a)
    (hn : Fiber.tensor M weight labels ≠ 0)
    (hs : MatchingCard.PairSafe (Fiber.tensor M weight labels))
    (hfactor : ¬ Fiber.HasProperTensorFactor (Fiber.tensor M weight labels)) :
    ∀ a, weight a ≠ 0 := by
  classical
  obtain ⟨e,f,hde,hdf,hef⟩ := two_other_edges hr distinguished
  have hc := live_count M weight labels distinguished e f hde hdf hef hlabel hs
  rcases hc with hz | hone | hfour
  · have hex : ∃ a, weight a ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn ((Fiber.zero_iff M weight labels distinguished hlabel).mpr h)
    obtain ⟨a,ha⟩ := hex
    have hp : 0 < Fintype.card {a : Label // weight a ≠ 0} :=
      Fintype.card_pos_iff.mpr ⟨⟨a,ha⟩⟩
    omega
  · obtain ⟨a,ha⟩ := Fintype.card_eq_one_iff.mp hone
    have hconstant : ∀ t, weight t ≠ 0 → labels t distinguished = a.val := by
      intro t ht
      rw [hlabel]
      exact congrArg Subtype.val (ha ⟨t,ht⟩)
    exact False.elim (hfactor (Fiber.constant_edge_factor M (by omega) weight labels
      distinguished a.val hn hconstant))
  · exact all_of_card_four (fun a => weight a ≠ 0) hfour

/-- Every label map is an actual permutation, selected from the SAME complete
fibre and derived live rows. This is the fixed-ruling fibre dichotomy. -/
def fullPermutation (M : Matching P r) (hr : 3 ≤ r)
    (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished : Fin r) (hlabel : ∀ a, labels a distinguished = a)
    (hn : Fiber.tensor M weight labels ≠ 0)
    (hs : MatchingCard.PairSafe (Fiber.tensor M weight labels))
    (hfactor : ¬ Fiber.HasProperTensorFactor (Fiber.tensor M weight labels))
    (e : Fin r) : Equiv.Perm Label :=
  labelPermutation M (by omega) weight labels distinguished hlabel hn hs hfactor
    (all_live M hr weight labels distinguished hlabel hn hs hfactor) e

@[simp] theorem fullPermutation_apply (M : Matching P r) (hr : 3 ≤ r)
    (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished : Fin r) (hlabel : ∀ a, labels a distinguished = a)
    (hn : Fiber.tensor M weight labels ≠ 0)
    (hs : MatchingCard.PairSafe (Fiber.tensor M weight labels))
    (hfactor : ¬ Fiber.HasProperTensorFactor (Fiber.tensor M weight labels))
    (e : Fin r) (a : Label) :
    fullPermutation M hr weight labels distinguished hlabel hn hs hfactor e a = labels a e := rfl

/-- Arity>=8 closed source of full live/permutation fibre data. The ONLY tensor
hypotheses are nonzero, actual ordered pair safety and genuine nonfactorhood. -/
theorem common_full_permutation_fiber (r : ℕ) (hr : 0 < r)
    (f : Signature ℂ (2*r+6)) (hf : f ≠ 0)
    (hs : MatchingCard.OrderedPairSafe f) (hfactor : ¬ Fiber.HasProperTensorFactor f) :
    ∃ s : ℕ, ∃ M : Matching (Fin (2*r+6)) (s+1),
      ∃ weight : Label → ℂ, ∃ labels : Label → Fin (s+1) → Label,
        (∀ a, labels a 0 = a) ∧ f = Fiber.tensor M weight labels ∧
        (∀ a, weight a ≠ 0) ∧
        (∀ e, Function.Bijective (fun a => labels a e)) ∧ 3 ≤ s := by
  obtain ⟨s,M,weight,labels,hlabel,he,hzero,hsz⟩ :=
    MatchingCard.common_full_fiber r hr f hf hs
  have hn : Fiber.tensor M weight labels ≠ 0 := he ▸ hf
  have hsafe : MatchingCard.PairSafe (Fiber.tensor M weight labels) :=
    he ▸ (MatchingCard.pairSafe_iff_ordered f).mpr hs
  have hnf : ¬ Fiber.HasProperTensorFactor (Fiber.tensor M weight labels) := he ▸ hfactor
  refine ⟨s,M,weight,labels,hlabel,he,
    all_live M (by omega) weight labels 0 hlabel hn hsafe hnf,?_,hsz⟩
  intro e
  exact (fullPermutation M (by omega) weight labels 0 hlabel hn hsafe hnf e).bijective

end
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
