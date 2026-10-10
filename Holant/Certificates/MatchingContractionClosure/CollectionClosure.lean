import Holant.Certificates.MatchingContractionClosure.EmptyCollection
import Holant.Certificates.MatchingContractionClosure.NonzeroProducts

namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
universe u v w z
variable {K : Type u} [Field K]

/-- Induction removes one actual original pair from the complete assignment
sum. This covers closed components as well as paths and preserves the zero
branch after any vanishing cycle trace. -/
theorem contractCollection_closed {G : Set (Binary (K := K))} (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := K)) ∈ G) (hrev : ReversalStable G)
    {P : Type v} [DecidableEq P] {Q : Type w} {E : Type z} [Fintype E] [DecidableEq E]
    (p : CollectionPorts P Q E) (C : E → Binary (K := K)) (F : Tensor K P)
    (hC : ∀ e, SafeBinary G (C e)) (hF : MatchingOrZero G F) :
    MatchingOrZero G (contractCollection p C F) := by
  classical
  have aux : ∀ n : ℕ, ∀ (E : Type z) [Fintype E] [DecidableEq E], Fintype.card E=n →
      ∀ (P : Type v) [DecidableEq P] (Q : Type w), ∀ p : CollectionPorts P Q E,
      ∀ C : E → Binary (K := K), ∀ F : Tensor K P,
      (∀ e, SafeBinary G (C e)) → MatchingOrZero G F → MatchingOrZero G (contractCollection p C F) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E _ _ hn P _ Q p C F hC hF
      rcases isEmpty_or_nonempty E with hE | hE
      · letI : IsEmpty E := hE
        rw [contractCollection_empty]
        exact MatchingOrZero.reindex hF (emptyBoundary p).symm
      · obtain ⟨e⟩ := hE
        have hl : Fintype.card (OtherEdges e)<n := by rw [← hn]; exact otherEdges_card_lt e
        have hpair := contractPair_closed hG hX hrev (p (.inr (e,false))) (p (.inr (e,true)))
          (collection_pair_distinct p e) (C e) (hC e) F hF
        rw [contractCollection_step p C F e]
        exact ih (Fintype.card (OtherEdges e)) hl (OtherEdges e) rfl
          (Remaining (p (.inr (e,false))) (p (.inr (e,true)))) Q (collectionTailPorts p e)
          (fun d => C d.val) _ (fun d => hC d.val) hpair
  exact aux (Fintype.card E) E rfl P Q p C F hC hF

/-- Unpack the source meaning of the result: either the whole output is zero,
or its actual surviving perfect-matching factors are nonsingular and all
their actual native-X transfers remain in G. -/
theorem contractCollection_factorization {G : Set (Binary (K := K))} (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := K)) ∈ G) (hrev : ReversalStable G)
    {P : Type v} [DecidableEq P] {Q : Type w} {E : Type z} [Fintype E] [DecidableEq E]
    (p : CollectionPorts P Q E) (C : E → Binary (K := K)) (F : Tensor K P)
    (hC : ∀ e, SafeBinary G (C e)) (hF : MatchingOrZero G F) :
    contractCollection p C F=0 ∨ ∃ M : Presentation K Q,
      contractCollection p C F=M.tensor ∧ M.scalar≠0 ∧
      ∀ e, Matrix.det (M.matrix e)≠0 ∧ transfer (M.matrix e) ∈ G := by
  rcases contractCollection_closed hG hX hrev p C F hC hF with hz | ⟨M,hM,hκ,hout⟩
  · exact Or.inl hz
  · exact Or.inr ⟨M,hout,hκ,fun e => ⟨SafeBinary.nonsingular hG (hM e),hM e⟩⟩

end
end Holant.Certificates.MatchingContractionClosure
