import Holant.OneHot.Decomposition.Components
import Holant.OneHot.Density

/-!
# Exact connected-component factorization

The independent half-edge assignment types are explicitly put in bijection.
Finite distributivity then proves factorization of the actual network denotation,
for arbitrary commutative-semiring labels, not just one-hot or native-X labels.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.NetworkShape

/-- All assignments split uniquely into assignments of all component edges.
Neither endpoint is dropped, and loops still have two independently assigned ends. -/
def componentAssignments (s : NetworkShape 0) :
    ((Fin s.edges × Bool) → Bool) ≃
      ((c : s.Component) → (s.ComponentEdge c × Bool) → Bool) where
  toFun z _ q := z (q.1.1, q.2)
  invFun z q := z (s.edgeComponent q.1) (⟨q.1, rfl⟩, q.2)
  left_inv _ := rfl
  right_inv z := by
    funext c q
    rcases q with ⟨⟨e, he⟩, b⟩
    subst c
    rfl

@[simp] theorem componentAssignments_apply (s : NetworkShape 0)
    (z : (Fin s.edges × Bool) → Bool) (c : s.Component)
    (q : s.ComponentEdge c × Bool) :
    s.componentAssignments z c q = z (q.1.1, q.2) := rfl

end Holant.NetworkShape

namespace Holant.Network

variable {K : Type*} [CommSemiring K]

/-- The actual half-edge summand of the restricted network. -/
noncomputable def componentTerm (N : Network K 0) (c : N.shape.Component)
    (z : (N.shape.ComponentEdge c × Bool) → Bool) : K := by
  classical
  exact (∏ v : N.shape.ComponentVertex c,
    N.vertex v.1 (fun i => z (N.shape.componentClosedPorts c ⟨v, i⟩))) *
    ∏ e : N.shape.ComponentEdge c, N.edge e.1 (z (e, false)) (z (e, true))

open scoped Classical in
/-- Restriction changes no vertex weight or native edge weight. -/
theorem denote_componentFiniteNetwork (N : Network K 0) (c : N.shape.Component)
    (x : Fin 0 → Bool) :
    (N.componentFiniteNetwork c).denote x =
      ∑ z : (N.shape.ComponentEdge c × Bool) → Bool, N.componentTerm c z := by
  classical
  simp [FiniteNetwork.denote, componentFiniteNetwork, componentTerm,
    NetworkShape.componentPorts, Equiv.emptySum]
  congr 1
  ext
  simp

open scoped Classical in
/-- Partition the original summand itself, counting every labelled object once. -/
theorem componentTerm_product (N : Network K 0) (x : Fin 0 → Bool)
    (z : (Fin N.shape.edges × Bool) → Bool) :
    (∏ c : N.shape.Component, N.componentTerm c (N.shape.componentAssignments z c)) =
      (∏ v : Fin N.shape.vertices, N.vertex v (N.shape.assignment x z v)) *
      ∏ e : Fin N.shape.edges, N.edge e (z (e, false)) (z (e, true)) := by
  classical
  simp only [componentTerm, NetworkShape.componentAssignments_apply,
    NetworkShape.componentClosedPorts_val, Finset.prod_mul_distrib]
  apply congrArg₂ (· * ·)
  · have ha : ∀ v, N.shape.assignment x z v =
        fun i => z (N.shape.closedPorts ⟨v, i⟩) :=
      fun v => funext (N.shape.assignment_closed x z v)
    simp only [ha]
    exact Fintype.prod_fiberwise N.shape.componentOf
      (fun v => N.vertex v (fun i => z (N.shape.closedPorts ⟨v, i⟩)))
  · exact Fintype.prod_fiberwise N.shape.edgeComponent
      (fun e => N.edge e (z (e, false)) (z (e, true)))

open scoped Classical in
/-- Exact factorization over genuine connected components of an arbitrary input.
This is proved from the defining sum; it is not a decomposition hypothesis. -/
theorem denote_eq_prod_componentFiniteNetwork (N : Network K 0) (x : Fin 0 → Bool) :
    N.denote x = ∏ c : N.shape.Component, (N.componentFiniteNetwork c).denote x := by
  classical
  simp only [denote_componentFiniteNetwork]
  rw [Fintype.prod_sum]
  unfold denote
  calc
    _ = ∑ z : (Fin N.shape.edges × Bool) → Bool,
        ∏ c : N.shape.Component, N.componentTerm c (N.shape.componentAssignments z c) := by
      apply Finset.sum_congr rfl
      intro z _
      exact (N.componentTerm_product x z).symm
    _ = _ := N.shape.componentAssignments.sum_comp
      (fun z => ∏ c : N.shape.Component, N.componentTerm c (z c))

open scoped Classical in
/-- Factorization into ordinary `Network` objects, preserving their full semantics. -/
theorem denote_eq_prod_componentNetwork (N : Network K 0) (x : Fin 0 → Bool) :
    N.denote x = ∏ c : N.shape.Component, (N.componentNetwork c).denote x := by
  classical
  rw [N.denote_eq_prod_componentFiniteNetwork x]
  apply Finset.prod_congr rfl
  intro c _
  exact congrFun (FiniteNetwork.denote_toNetwork (N.componentFiniteNetwork c)).symm x

/-- Restriction retains the one-hot property with exactly the same local port order. -/
theorem componentNetwork_oneHot (N : Network K 0)
    (hf : ∀ v, Signature.OneHot (N.vertex v)) (c : N.shape.Component)
    (v : Fin (N.componentNetwork c).shape.vertices) :
    Signature.OneHot ((N.componentNetwork c).vertex v) := by
  classical
  exact hf ((Fintype.equivFin (N.shape.ComponentVertex c)).symm v).1

/-- Restriction retains the original native-X edge tensor, without pins or scalars. -/
theorem componentNetwork_native (N : Network K 0)
    (hX : ∀ e, N.edge e = Signature.disequality) (c : N.shape.Component)
    (e : Fin (N.componentNetwork c).shape.edges) :
    (N.componentNetwork c).edge e = Signature.disequality := by
  classical
  exact hX ((Fintype.equivFin (N.shape.ComponentEdge c)).symm e).1

/-- A dense component kills the whole network, even if other components contain
many isolated vertices and the *global* edge count is below the vertex count. -/
theorem denote_native_oneHot_of_dense_component (N : Network K 0)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) (c : N.shape.Component)
    (hdense : Nat.card (N.shape.ComponentVertex c) < Nat.card (N.shape.ComponentEdge c)) :
    N.denote = 0 := by
  classical
  have hd : (N.componentNetwork c).shape.vertices < (N.componentNetwork c).shape.edges := by
    simpa only [componentNetwork_vertices, componentNetwork_edges] using hdense
  have hzero : (N.componentNetwork c).denote = 0 := by
    have hn := denote_native_oneHot_of_dense (N.componentNetwork c).shape
      (N.componentNetwork c).vertex (N.componentNetwork_oneHot hf c) hd
    apply Eq.trans ?_ hn
    apply denote_congr
    · intro v x
      rfl
    · intro e a b
      exact congrFun₂ (N.componentNetwork_native hX c e) a b
  funext x
  rw [N.denote_eq_prod_componentNetwork x]
  exact Finset.prod_eq_zero (Finset.mem_univ c) (congrFun hzero x)

end Holant.Network
