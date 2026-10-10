import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFixedRuling

/-! Named original-port formulation of the fixed-ruling theorem. Transport
changes only the physical port names, with the ordered kernel unchanged. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.TwoCardLocalization
open Holant.Dihedral.CompatibleClosure (pairOrder)

namespace MatchingSurgery
variable {K P Q : Type*} [Field K] [DecidableEq P] [DecidableEq Q]

def remainingMap (e : P ≃ Q) (u v : P) : Remaining u v ≃ Remaining (e u) (e v) :=
  e.subtypeEquiv (fun i => by simp only [ne_eq,e.injective.eq_iff])

theorem contractPair_reindex (e : P ≃ Q) (u v : P) (huv : u ≠ v)
    (C : Kernel K) (f : Tensor K P) :
    contractPair (e u) (e v) C (Tensor.reindex e f) =
      Tensor.reindex (remainingMap e u v) (contractPair u v C f) := by
  funext x
  have hw (a b : Bool) :
      (fun i => insertPair (e u) (e v) a b (extendRemaining (e u) (e v) x) (e i)) =
        insertPair u v a b (extendRemaining u v (fun j => x (remainingMap e u v j))) := by
    funext i
    by_cases hi : i = u
    · subst i
      rw [insertPair_first (fun h => huv (e.injective h)),insertPair_first huv]
    by_cases hj : i = v
    · subst i
      rw [insertPair_second,insertPair_second]
    rw [insertPair_other (fun h => hi (e.injective h)) (fun h => hj (e.injective h)),
      insertPair_other hi hj]
    simp only [extendRemaining,hi,hj,ne_eq,e.injective.eq_iff,not_false_eq_true,and_self,
      dite_true,remainingMap,Equiv.subtypeEquiv_apply]
  simp only [contractPair,Tensor.reindex,hw]

end MatchingSurgery

namespace MatchingCard

/-- All literal pair contractions on the original physical port set. -/
def PairSafe {P : Type*} [DecidableEq P] (f : Tensor ℂ P) : Prop :=
  ∀ u v : P, u ≠ v → ∀ a : Label,
    PauliMatchingOrZero (contractPair u v (asMatrix (dual a)) f)

theorem pairSafe_reindex {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (e : P ≃ Q) (f : Tensor ℂ P) (hf : PairSafe f) : PairSafe (Tensor.reindex e f) := by
  intro u v huv a
  obtain ⟨u,rfl⟩ := e.surjective u
  obtain ⟨v,rfl⟩ := e.surjective v
  have hne : u ≠ v := fun h => huv (congrArg e h)
  change PauliMatchingOrZero (contractPair (e u) (e v) (dual a) (Tensor.reindex e f))
  rw [MatchingSurgery.contractPair_reindex e u v hne (dual a) f]
  exact Pauli_reindex _ _ (hf u v hne a)

theorem pairSafe_iff_ordered {n : ℕ} (f : Signature ℂ (n+2)) :
    PairSafe f ↔ OrderedPairSafe f := by
  constructor
  · intro hf p a
    have hh := pairSafe_reindex p.symm f hf 0 1 Fin.zero_ne_one a
    have hr := Pauli_reindex (remainingOrder (0 : Fin (n+2)) 1 Fin.zero_ne_one).symm _ hh
    change PauliMatchingOrZero (Tensor.reindex (remainingOrder 0 1 Fin.zero_ne_one).symm
      (contractPair 0 1 (dual a) (Tensor.reindex p.symm f))) at hr
    rwa [contractPair_front] at hr
  · intro hf u v huv a
    apply (Pauli_reindex_iff (remainingOrder u v huv).symm _).mp
    change PauliMatchingOrZero (Tensor.reindex (remainingOrder u v huv).symm (contractPair u v (dual a) f))
    rw [contractPair_order u v huv (dual a) f]
    exact hf (pairOrder u v) a

theorem fixed_ruling_physical (r : ℕ) (hr : 0 < r) (f : Signature ℂ (2*r+6))
    (hf : f ≠ 0) (hs : PairSafe f) (u v : Fin (2*r+6)) (huv : u ≠ v) :
    ∃ s : ℕ, ∃ M : Matching (Remaining u v) s,
      ∀ a : Label, ∀ t : ℕ, ∀ N : Matching (Remaining u v) t,
        ∀ labels : Fin t → Label, ∀ c : ℂ, c ≠ 0 →
        contractPair u v (asMatrix (dual a)) f = (fun x => c*N.tensor labels x) →
        N.mate = M.mate := by
  let e := remainingOrder u v huv
  obtain ⟨s,M,hM⟩ := fixed_ruling r hr f hf ((pairSafe_iff_ordered f).mp hs) (pairOrder u v)
  refine ⟨s,⟨M.ports.trans e⟩,?_⟩
  intro a t N labels c hc hN
  let N' : Matching (Fin (2*r+4)) t := ⟨N.ports.trans e.symm⟩
  have he : Signature.contract (dual a) (Tensor.reindex (pairOrder u v).symm f) =
      fun x => c*N'.tensor labels x := by
    rw [←contractPair_order u v huv (dual a) f]
    exact congrArg (Tensor.reindex e.symm) hN
  have hh := hM a t N' labels c hc he
  apply Equiv.ext
  intro i
  have hi := congrArg (fun m : Equiv.Perm (Fin (2*r+4)) => m (e.symm i)) hh
  have hi' := congrArg e hi
  simpa [N',Matching.mate] using hi'

end MatchingCard
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
