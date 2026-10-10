import Holant.Pauli.ExoticKlein.FiberDichotomy

/-! Public all-original-port form of the fixed-ruling fiber dichotomy,
source Lemma 8.7. No tomographic normal form or finite support pattern is an
input hypothesis; both are derived from the actual proper cards. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Holant.Dihedral.CompatibleCoefficientLine (pair tail)
open Holant.Dihedral.CompatibleClosure (pairOrder)
open Holant.Dihedral.TwoCardLocalization
open Holant.Certificates.MatchingContractionClosure
namespace MatchingCard

theorem ordered_fiber_dichotomy (r : ℕ) (hr : 0 < r) (f : Signature ℂ (2*r+6))
    (hf : f ≠ 0) (hs : OrderedPairSafe f) (hp : ¬ Fiber.HasProperTensorFactor f) :
    ∃ s : ℕ, ∃ M : Matching (Fin (2*r+4)) s,
      ∃ weight : Label → ℂ, ∃ permutations : Fin s → Equiv.Perm Label,
        3 ≤ s ∧ (∀ a, weight a ≠ 0) ∧
        ∀ a, Signature.contract (dual a) f ≠ 0 ∧
          Signature.contract (dual a) f = fun x => weight a*M.tensor (fun e => permutations e a) x := by
  obtain ⟨s,M,weight,labels,he,hz⟩ := common_card_coordinates r hr f hf hs
  have hcard := M.port_card
  simp only [Fintype.card_fin] at hcard
  let labels' : Label → Fin (s+1) → Label := fun a => Fin.cons a (labels a)
  have hfull : f = Fiber.tensor M.prepend weight labels' := by
    funext x
    have hx : pair (x 0) (x 1) (tail x) = x := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
    have hh := front_reconstruction f (x 0) (x 1) (tail x)
    rw [hx] at hh
    rw [←hh]
    simp only [Fiber.tensor,labels',Matching.prepend_tensor,he]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hs' : PairSafe (Fiber.tensor M.prepend weight labels') := by
    rw [←hfull]
    exact (pairSafe_iff_ordered f).mpr hs
  have hn' : Fiber.tensor M.prepend weight labels' ≠ 0 := by rwa [←hfull]
  have hp' : ¬ Fiber.HasProperTensorFactor (Fiber.tensor M.prepend weight labels') := by rwa [←hfull]
  obtain ⟨hw,hbij⟩ := Fiber.dichotomy M.prepend (by omega) weight labels' 0 (fun _ => rfl) hs' hn' hp'
  let perms : Fin s → Equiv.Perm Label := fun e => Equiv.ofBijective (fun a => labels a e) (hbij e.succ)
  refine ⟨s,M,weight,perms,by omega,hw,?_⟩
  intro a
  refine ⟨?_,he a⟩
  rw [he]
  exact scaled_matching_ne_zero M (labels a) (weight a) (hw a)

/-- Every one of the four actual cards is nonzero, and on the one residual
original-port matching every local label map is an actual permutation. -/
theorem fiber_dichotomy_physical (r : ℕ) (hr : 0 < r) (f : Signature ℂ (2*r+6))
    (hf : f ≠ 0) (hs : PairSafe f) (hp : ¬ Fiber.HasProperTensorFactor f)
    (u v : Fin (2*r+6)) (huv : u ≠ v) :
    ∃ s : ℕ, ∃ M : Matching (Remaining u v) s,
      ∃ weight : Label → ℂ, ∃ permutations : Fin s → Equiv.Perm Label,
        3 ≤ s ∧ (∀ a, weight a ≠ 0) ∧
        ∀ a, contractPair u v (asMatrix (dual a)) f ≠ 0 ∧
          contractPair u v (asMatrix (dual a)) f = fun x => weight a*M.tensor (fun e => permutations e a) x := by
  let p := pairOrder u v
  let q := Tensor.reindex p.symm f
  have hq : q ≠ 0 := by
    intro hz
    have hh := congrArg (Tensor.reindex p) hz
    have he : Tensor.reindex p q = f := by
      funext x
      simp only [q,Tensor.reindex,Equiv.apply_symm_apply]
    rw [he] at hh
    exact hf hh
  have hsafe := (pairSafe_iff_ordered q).mp (pairSafe_reindex p.symm f hs)
  have hprime : ¬ Fiber.HasProperTensorFactor q :=
    fun h => hp ((Fiber.factor_reindex_iff p.symm f).mp h)
  obtain ⟨s,M,weight,perms,hsize,hw,hcards⟩ := ordered_fiber_dichotomy r hr q hq hsafe hprime
  let e := remainingOrder u v huv
  refine ⟨s,⟨M.ports.trans e⟩,weight,perms,hsize,hw,?_⟩
  intro a
  have hh := congrArg (Tensor.reindex e) (hcards a).2
  change Tensor.reindex e (Signature.contract (dual a) (Tensor.reindex (pairOrder u v).symm f)) = _ at hh
  rw [←contractPair_order u v huv (dual a) f] at hh
  have he : contractPair u v (asMatrix (dual a)) f =
      fun x => weight a*(⟨M.ports.trans e⟩ : Matching (Remaining u v) s).tensor (fun i => perms i a) x := by
    change contractPair u v (dual a) f = Tensor.reindex e (fun x => weight a*M.tensor (fun i => perms i a) x)
    simpa only [e,Tensor.reindex_trans,Equiv.symm_trans_self,Tensor.reindex_refl] using hh
  refine ⟨?_,he⟩
  rw [he]
  exact scaled_matching_ne_zero ⟨M.ports.trans e⟩ (fun i => perms i a) (weight a) (hw a)

end MatchingCard
end
end Holant.Pauli.ExoticKlein
