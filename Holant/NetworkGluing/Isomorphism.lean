import Holant.NetworkGluing.Finite

/-!
# Exact isomorphisms of ordered-port finite networks

The data explicitly identify vertices, edges, boundary order, every local port,
and the orientation of each edge. Compatibility concerns only incidence and
literal labels. Equality of the actual assignment sums is then proved, never
included as an assumption. Loops, parallel edges and nullary vertices require
no exceptional case.
-/

namespace Holant.FiniteNetwork

variable {K V V' E E' : Type*} {m n : ℕ}

/-- An edge relabelling together with an independent endpoint-order permutation
for each original edge. -/
def edgeEndEquiv (edges : E ≃ E') (orientations : E → Bool ≃ Bool) :
    (E × Bool) ≃ (E' × Bool) where
  toFun q := (edges q.1, orientations q.1 q.2)
  invFun q := (edges.symm q.1, (orientations (edges.symm q.1)).symm q.2)
  left_inv q := by rcases q with ⟨e, b⟩; simp
  right_inv q := by rcases q with ⟨e, b⟩; simp

/-- Full concrete graph isomorphism. Port compatibility explicitly transports
the given input tables and edge kernels, including asymmetric kernels. -/
structure Isomorphism (L : FiniteNetwork K V E m) (R : FiniteNetwork K V' E' n) where
  vertices : V ≃ V'
  edges : E ≃ E'
  boundary : Fin m ≃ Fin n
  ports : (v : V) → Fin (L.arity v) ≃ Fin (R.arity (vertices v))
  orientations : E → Bool ≃ Bool
  incidence : ∀ (v : V) (i : Fin (L.arity v)),
    R.ports ⟨vertices v, ports v i⟩ =
      (Equiv.sumCongr boundary (edgeEndEquiv edges orientations)) (L.ports ⟨v, i⟩)
  vertex_labels : ∀ (v : V) (y : Fin (R.arity (vertices v)) → Bool),
    R.vertex (vertices v) y = L.vertex v (fun i => y (ports v i))
  edge_labels : ∀ (e : E) (y : Bool → Bool),
    R.edge (edges e) (y false) (y true) =
      L.edge e (y (orientations e false)) (y (orientations e true))

namespace Isomorphism

variable {L : FiniteNetwork K V E m} {R : FiniteNetwork K V' E' n}
    (h : Isomorphism L R)

/-- Every independent source endpoint bit moves bijectively to its target bit. -/
def assignments : ((E × Bool) → Bool) ≃ ((E' × Bool) → Bool) :=
  Equiv.arrowCongr (edgeEndEquiv h.edges h.orientations) (Equiv.refl Bool)

@[simp] theorem assignments_end (z : (E × Bool) → Bool) (e : E) (b : Bool) :
    h.assignments z (h.edges e, h.orientations e b) = z (e, b) := by
  simp [assignments, edgeEndEquiv]

/-- Evaluation of each original port is unchanged after the complete transport. -/
theorem assignment_port (x : Fin n → Bool) (z : (E × Bool) → Bool)
    (v : V) (i : Fin (L.arity v)) :
    Sum.elim x (h.assignments z) (R.ports ⟨h.vertices v, h.ports v i⟩) =
      Sum.elim (fun j => x (h.boundary j)) z (L.ports ⟨v, i⟩) := by
  rw [h.incidence]
  cases hp : L.ports ⟨v, i⟩ with
  | inl j => rfl
  | inr q => exact h.assignments_end z q.1 q.2

set_option backward.isDefEq.respectTransparency false in
/-- Exact denotation transport under actual finite graph isomorphism. -/
theorem denote [Fintype V] [Fintype V'] [Fintype E] [Fintype E']
    [CommSemiring K] (x : Fin n → Bool) :
    L.denote (fun j => x (h.boundary j)) = R.denote x := by
  classical
  unfold FiniteNetwork.denote
  apply Fintype.sum_equiv h.assignments
  intro z
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv h.vertices
    intro v
    rw [h.vertex_labels]
    congr 1
    funext i
    exact (h.assignment_port x z v i).symm
  · apply Fintype.prod_equiv h.edges
    intro e
    rw [h.edge_labels e (fun b => h.assignments z (h.edges e, b))]
    simp only [h.assignments_end]

/-- Signature-level form, with the boundary permutation exposed explicitly. -/
theorem denote_reindex [Fintype V] [Fintype V'] [Fintype E] [Fintype E']
    [CommSemiring K] : Tensor.reindex h.boundary L.denote = R.denote := by
  funext x
  exact h.denote x

/-- Enumerating either finite presentation by `Fin` does not alter this bridge. -/
theorem denote_toNetwork_reindex [Fintype V] [Fintype V'] [Fintype E] [Fintype E']
    [CommSemiring K] : Tensor.reindex h.boundary L.toNetwork.denote = R.toNetwork.denote := by
  rw [FiniteNetwork.denote_toNetwork, FiniteNetwork.denote_toNetwork]
  exact h.denote_reindex

end Isomorphism
end Holant.FiniteNetwork
