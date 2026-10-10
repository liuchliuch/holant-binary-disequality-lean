import Holant.ReedMuller.FlatNetwork.NamedPorts

/-! Closure for the complete simultaneous contraction of an arbitrary finite
collection of disjoint original ports. Closed components are included. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.Certificates.MatchingContractionClosure
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w

theorem flatTensorOrZero_contractCollection
    {P : Type u} [Fintype P] [DecidableEq P] {Q : Type v}
    {E : Type w} [Fintype E] [DecidableEq E]
    (p : CollectionPorts P Q E) (eta : E → ZMod 2) (F : Tensor ℂ P)
    (hF : FlatTensorOrZero F) :
    FlatTensorOrZero (contractCollection p (fun e => parityKernel (eta e)) F) := by
  classical
  have aux : ∀ n : ℕ, ∀ (E : Type w) [Fintype E] [DecidableEq E],Fintype.card E=n →
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (Q : Type v),
      ∀ p : CollectionPorts P Q E,∀ eta : E → ZMod 2,∀ F : Tensor ℂ P,
      FlatTensorOrZero F → FlatTensorOrZero (contractCollection p (fun e => parityKernel (eta e)) F) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E _ _ hn P _ _ Q p eta F hF
      rcases isEmpty_or_nonempty E with hE | hE
      · letI : IsEmpty E := hE
        rw [contractCollection_empty]
        exact hF.reindex (emptyBoundary p).symm
      · obtain ⟨e⟩ := hE
        have hl : Fintype.card (OtherEdges e)<n := by rw [←hn];exact otherEdges_card_lt e
        have hc := flatTensorOrZero_contractPair (p (.inr (e,false))) (p (.inr (e,true)))
          (collection_pair_distinct p e) (eta e) F hF
        rw [contractCollection_step p _ F e]
        exact ih (Fintype.card (OtherEdges e)) hl (OtherEdges e) rfl
          (Remaining (p (.inr (e,false))) (p (.inr (e,true)))) Q (collectionTailPorts p e)
          (fun d => eta d.val) _ hc
  exact aux (Fintype.card E) E rfl P Q p eta F hF

end
end Holant.ReedMuller.FlatNetwork
