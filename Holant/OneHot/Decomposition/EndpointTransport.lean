import Holant.NetworkGluing.Isomorphism
import Holant.OneHot.Representation
import Holant.OneHot.Decomposition.Components

/-! Recover every local ordered-port permutation from complete endpoint transport. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.FiniteNetwork

variable {K V V' E E' : Type*}

/-- A closed finite network's literal ordered occurrence bijection. -/
def closedPorts (N : FiniteNetwork K V E 0) :
    (Σ v, Fin (N.arity v)) ≃ (E × Bool) :=
  N.ports.trans (Equiv.emptySum _ _)

/-- The original vertex at a named oriented edge endpoint. -/
def endpoint (N : FiniteNetwork K V E 0) (e : E) (b : Bool) : V :=
  (N.closedPorts.symm (e, b)).1

/-- Preserve local argument order when identifying a vertex's occurrence fiber. -/
def localOccurrenceEquiv (N : FiniteNetwork K V E 0) (v : V) :
    Fin (N.arity v) ≃ {p : Σ w, Fin (N.arity w) // p.1 = v} where
  toFun i := ⟨⟨v, i⟩, rfl⟩
  invFun p := p.2 ▸ p.1.2
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨w, i⟩, h⟩; cases h; rfl

/-- Each original local port bijects with the exact incident endpoint fiber. -/
def localEndFiberEquiv (N : FiniteNetwork K V E 0) (v : V) :
    Fin (N.arity v) ≃ {q : E × Bool // N.endpoint q.1 q.2 = v} :=
  (N.localOccurrenceEquiv v).trans (N.closedPorts.subtypeEquiv (fun p => by
    simp only [endpoint, Prod.eta, Equiv.symm_apply_apply]))

@[simp] theorem localEndFiberEquiv_val (N : FiniteNetwork K V E 0) (v : V)
    (i : Fin (N.arity v)) : (N.localEndFiberEquiv v i).1 = N.closedPorts ⟨v, i⟩ := rfl

/-- Complete endpoint-level graph transport. The local port equivalences below
are derived from this data, rather than silently assumed. -/
structure EndpointTransport (L : FiniteNetwork K V E 0) (R : FiniteNetwork K V' E' 0) where
  vertices : V ≃ V'
  edges : E ≃ E'
  orientations : E → Bool ≃ Bool
  endpoints : ∀ e b, R.endpoint (edges e) (orientations e b) = vertices (L.endpoint e b)

namespace EndpointTransport

variable {L : FiniteNetwork K V E 0} {R : FiniteNetwork K V' E' 0}
variable (h : EndpointTransport L R)

/-- The bijection contains both original endpoints of every edge. -/
def ends : (E × Bool) ≃ (E' × Bool) := edgeEndEquiv h.edges h.orientations

/-- Recover the exact local port permutation for every original vertex. -/
def ports (v : V) : Fin (L.arity v) ≃ Fin (R.arity (h.vertices v)) :=
  (L.localEndFiberEquiv v).trans
    ((h.ends.subtypeEquiv (fun q => by
      change L.endpoint q.1 q.2 = v ↔
        R.endpoint (h.edges q.1) (h.orientations q.1 q.2) = h.vertices v
      rw [h.endpoints]
      exact h.vertices.injective.eq_iff.symm)).trans
        (R.localEndFiberEquiv (h.vertices v)).symm)

/-- The derived local permutation preserves the whole original edge-end identity. -/
theorem closed_incidence (v : V) (i : Fin (L.arity v)) :
    R.closedPorts ⟨h.vertices v, h.ports v i⟩ = h.ends (L.closedPorts ⟨v, i⟩) := by
  have hp := (R.localEndFiberEquiv (h.vertices v)).apply_symm_apply
    ((h.ends.subtypeEquiv (fun q => by
      change L.endpoint q.1 q.2 = v ↔
        R.endpoint (h.edges q.1) (h.orientations q.1 q.2) = h.vertices v
      rw [h.endpoints]
      exact h.vertices.injective.eq_iff.symm)) (L.localEndFiberEquiv v i))
  exact congrArg Subtype.val hp

/-- Exact occurrence-level inverse image, retaining the original local index. -/
theorem target_occurrence (v : V) (i : Fin (L.arity v)) :
    (⟨h.vertices v, h.ports v i⟩ : Σ w, Fin (R.arity w)) =
      R.closedPorts.symm (h.ends (L.closedPorts ⟨v, i⟩)) := by
  apply R.closedPorts.injective
  rw [Equiv.apply_symm_apply]
  exact h.closed_incidence v i

/-- Turn proved endpoint transport and literal label compatibility into the
full network isomorphism, with no denotation premise. -/
def toIsomorphism
    (vertex_labels : ∀ v y, R.vertex (h.vertices v) y =
      L.vertex v (fun i => y (h.ports v i)))
    (edge_labels : ∀ e (y : Bool → Bool), R.edge (h.edges e) (y false) (y true) =
      L.edge e (y (h.orientations e false)) (y (h.orientations e true))) :
    Isomorphism L R where
  vertices := h.vertices
  edges := h.edges
  boundary := Equiv.refl _
  ports := h.ports
  orientations := h.orientations
  incidence v i := by
    apply (Equiv.emptySum (Fin 0) (E' × Bool)).injective
    change R.closedPorts ⟨h.vertices v, h.ports v i⟩ = _
    rw [h.closed_incidence]
    cases hp : L.ports ⟨v, i⟩ with
    | inl j => exact Fin.elim0 j
    | inr q => simp [closedPorts, hp, ends]
  vertex_labels := vertex_labels
  edge_labels := edge_labels

end EndpointTransport
end Holant.FiniteNetwork

namespace Holant.OneHot

variable {K : Type*} [CommSemiring K] {m n : ℕ}

/-- Canonical one-hot tables transport along every explicit local port bijection. -/
theorem table_reindex (p : Fin m ≃ Fin n) (a : K) (b : Fin n → K)
    (x : Fin n → Bool) :
    table a (fun i => b (p i)) (fun i => x (p i)) = table a b x := by
  have hw : weight (fun i => x (p i)) = weight x :=
    p.sum_comp (fun i => if x i then 1 else 0)
  unfold table
  rw [hw]
  rw [p.prod_comp (fun i => if x i then b i else 1)]

end Holant.OneHot

namespace Holant.Network

variable {K : Type*} {n : ℕ}

/-- View the same literal network with its existing finite vertex/edge types. -/
def asFinite (N : Network K n) : FiniteNetwork K (Fin N.shape.vertices) (Fin N.shape.edges) n where
  arity := N.shape.arity
  ports := N.shape.ports
  vertex := N.vertex
  edge := N.edge

@[simp] theorem denote_asFinite [CommSemiring K] (N : Network K n) :
    N.asFinite.denote = N.denote := by
  classical
  funext x
  unfold FiniteNetwork.denote Network.denote
  apply Finset.sum_congr
  · ext z
    simp
  · intro z _
    rfl

@[simp] theorem asFinite_endpoint (N : Network K 0) (e : Fin N.shape.edges) (b : Bool) :
    N.asFinite.endpoint e b = N.shape.endpoint e b := rfl

end Holant.Network
