import Holant.OpenNetworkComposition.OrdinaryNormalization.EmptyFree
import Holant.OpenNetworkComposition.OrdinaryNormalization.Step

/-! Exact conversion of an arbitrary native-X open gadget to an ordinary
ordered-port network using only its original vertex labels and literal I.
Every free stub is removed through an actual I-X-I splice; no wire circle or
scalar is discarded. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.OrdinaryNormalization
universe u v w z
variable {K : Type u} [CommSemiring K] {n : ℕ}

/-- All arbitrary finite-index free-stub gadgets can be made ordinary. The
induction counts actual free occurrences, including both ends of edge boxes. -/
theorem exists_ordinary {V : Type v} {F : Type w} {E : Type z}
    [Fintype V] [Fintype F] [Fintype E]
    (M : FiniteNetwork K V F E n) (family : SignatureFamily K)
    (hv : ∀v,(⟨M.shape.arity v,M.vertex v⟩ : AnySignature K)∈family)
    (he : ∀e,M.edge e=.disequality)
    (hI : (⟨2,identitySignature (K := K)⟩ : AnySignature K)∈family) :
    ∃ N : Network K n,
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote=M.tensor := by
  classical
  have aux : ∀k : ℕ,∀ (V : Type v) (F : Type w) (E : Type z)
      [Fintype V] [Fintype F] [Fintype E], Fintype.card F=k →
      ∀M : FiniteNetwork K V F E n,
      (∀v,(⟨M.shape.arity v,M.vertex v⟩ : AnySignature K)∈family) →
      (∀e,M.edge e=.disequality) →
      ∃ N : Network K n,
        (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
        (∀e,N.edge e=Signature.disequality) ∧ N.denote=M.tensor := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro V F E _ _ _ hk M hv he
      rcases isEmpty_or_nonempty F with hF | hF
      · let : IsEmpty F := hF
        exact exists_ordinary_of_isEmpty M family hv he
      · obtain ⟨f⟩ := hF
        have hl : Fintype.card (FiniteShape.CutFree f ⊕ WireFree)<k := by
          rw [←hk]
          exact step_free_card_lt f
        obtain ⟨N,hvN,heN,hN⟩ := ih _ hl _ _ _ rfl (step M f)
          (step_uses M f family hv hI) (step_native M f he)
        exact ⟨N,hvN,heN,hN.trans (step_tensor M f he)⟩
  exact aux _ V F E rfl M hv he

/-- The requested conversion starts from the actual OpenNetwork witness and
retains its tensor exactly, with native X edges and the original family. -/
theorem openNetwork_exists_ordinary (M : OpenNetwork K n) (family : SignatureFamily K)
    (hv : M.Uses family) (he : M.HasDefaultEdges .disequality)
    (hI : (⟨2,identitySignature (K := K)⟩ : AnySignature K)∈family) :
    ∃ N : Network K n,
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote=M.tensor := by
  obtain ⟨N,hvN,heN,hN⟩ := exists_ordinary (FiniteNetwork.ofOpen M) family hv he hI
  exact ⟨N,hvN,heN,hN.trans (FiniteNetwork.ofOpen_tensor M)⟩

/-- Arbitrary actual realization now yields an ordinary template. There is
no additional realization premise, normalization factor, or scalar resource. -/
theorem realizes_exists_ordinary {family : SignatureFamily K} {h : Signature K n}
    (hI : (⟨2,identitySignature (K := K)⟩ : AnySignature K)∈family)
    (hh : Gadget.Realizes family .disequality h) :
    ∃ N : Network K n,
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote=h := by
  obtain ⟨M,hv,he,hm⟩ := hh
  obtain ⟨N,hvN,heN,hN⟩ := openNetwork_exists_ordinary M family hv he hI
  exact ⟨N,hvN,heN,hN.trans hm⟩

/-- Projective input preserves its stated nonzero multiplier literally. -/
theorem realizesUpTo_exists_ordinary {family : SignatureFamily K} {h : Signature K n}
    (hI : (⟨2,identitySignature (K := K)⟩ : AnySignature K)∈family)
    (hh : Gadget.RealizesUpTo family .disequality h) :
    ∃ c : K,c≠0 ∧ ∃ N : Network K n,
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote=(fun x => c*h x) := by
  obtain ⟨c,hc,hreal⟩ := hh
  exact ⟨c,hc,realizes_exists_ordinary hI hreal⟩

end Holant.OpenNetworkComposition.OrdinaryNormalization
