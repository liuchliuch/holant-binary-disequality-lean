import Holant.OneHot.Decomposition.Extraction

/-!
# Denotation-preserving rooted multigraph presentations

The extracted parent/surplus edge partition is applied to the actual restricted
network. Vertices, local port numbers, labels, and the two endpoint orientations
are unchanged. This is not yet the recursive `Tree`/decorated-cycle evaluator
translation; it is its complete original-incidence input interface.
-/

namespace Holant.FiniteNetwork

variable {K V E E' : Type*} {n : ℕ}

/-- Reindex edges without changing any vertex or ordered local port. -/
def reindexEdges (N : FiniteNetwork K V E n) (r : E' ≃ E) :
    FiniteNetwork K V E' n where
  arity := N.arity
  ports := N.ports.trans (Equiv.sumCongr (Equiv.refl _)
    (Equiv.prodCongr r.symm (Equiv.refl _)))
  vertex := N.vertex
  edge e := N.edge (r e)

/-- Recovering the old edge identity recovers the exact old port incidence. -/
theorem reindexEdges_ports (N : FiniteNetwork K V E n) (r : E' ≃ E)
    (p : Σ v, Fin (N.arity v)) :
    (Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr r (Equiv.refl _)))
      ((N.reindexEdges r).ports p) = N.ports p := by
  change (Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr r (Equiv.refl _)))
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr r.symm (Equiv.refl _)))
      (N.ports p)) = N.ports p
  cases N.ports p with
  | inl i => rfl
  | inr q => rcases q with ⟨e, b⟩; simp

set_option backward.isDefEq.respectTransparency false in
/-- Exact equality of defining half-edge sums under the extracted edge partition. -/
theorem denote_reindexEdges [Fintype V] [Fintype E] [Fintype E'] [CommSemiring K]
    (N : FiniteNetwork K V E n) (r : E' ≃ E) :
    (N.reindexEdges r).denote = N.denote := by
  classical
  funext x
  unfold denote
  apply Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.prodCongr r (Equiv.refl Bool)) (Equiv.refl Bool))
  intro z
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    congr 1
    funext i
    dsimp [reindexEdges]
    cases N.ports ⟨v, i⟩ <;> rfl
  · apply Fintype.prod_equiv r
    intro e
    simp [reindexEdges]

end Holant.FiniteNetwork

namespace Holant.Network

variable {K : Type*}

/-- A finite presentation of a genuine input component as an extracted rooted
spanning tree plus all of its original surplus edges. No labels are synthesized. -/
noncomputable def componentSpanningNetwork (N : Network K 0) (c : N.shape.Component) :
    FiniteNetwork K (N.shape.ComponentVertex c)
      ({v : N.shape.ComponentVertex c // v ≠ N.shape.componentRoot c} ⊕
        (N.shape.componentSpanning c).Surplus) 0 :=
  (N.componentFiniteNetwork c).reindexEdges (N.shape.componentSpanning c).edgeEquiv

/-- Every original local argument remains at the same port number. -/
@[simp] theorem componentSpanningNetwork_arity (N : Network K 0)
    (c : N.shape.Component) (v : N.shape.ComponentVertex c) :
    (N.componentSpanningNetwork c).arity v = N.shape.arity v.1 := rfl

/-- Every original signature, including a nullary signature, is retained verbatim. -/
@[simp] theorem componentSpanningNetwork_vertex (N : Network K 0)
    (c : N.shape.Component) (v : N.shape.ComponentVertex c) :
    (N.componentSpanningNetwork c).vertex v = N.vertex v.1 := rfl

/-- The kernel on a selected parent edge is exactly its original edge kernel. -/
@[simp] theorem componentSpanningNetwork_parent_edge (N : Network K 0)
    (c : N.shape.Component)
    (v : {v : N.shape.ComponentVertex c // v ≠ N.shape.componentRoot c}) :
    (N.componentSpanningNetwork c).edge (.inl v) =
      N.edge ((N.shape.componentSpanning c).parentEdge v).1 := rfl

/-- Surplus edges retain their original kernels, including a possible loop. -/
@[simp] theorem componentSpanningNetwork_surplus_edge (N : Network K 0)
    (c : N.shape.Component) (e : (N.shape.componentSpanning c).Surplus) :
    (N.componentSpanningNetwork c).edge (.inr e) = N.edge e.1.1 := rfl

open scoped Classical in
/-- Exact semantic bridge for every extracted connected-component presentation. -/
theorem denote_componentSpanningNetwork [CommSemiring K] (N : Network K 0)
    (c : N.shape.Component) :
    (N.componentSpanningNetwork c).denote = (N.componentFiniteNetwork c).denote :=
  (N.componentFiniteNetwork c).denote_reindexEdges (N.shape.componentSpanning c).edgeEquiv

open scoped Classical in
/-- Full denotation factorization of an arbitrary input into its genuinely
extracted spanning-tree-plus-surplus presentations. -/
theorem denote_eq_prod_componentSpanningNetwork [CommSemiring K] (N : Network K 0)
    (x : Fin 0 → Bool) :
    N.denote x = ∏ c : N.shape.Component, (N.componentSpanningNetwork c).denote x := by
  rw [N.denote_eq_prod_componentFiniteNetwork x]
  apply Finset.prod_congr rfl
  intro c _
  exact congrFun (N.denote_componentSpanningNetwork c).symm x

end Holant.Network
