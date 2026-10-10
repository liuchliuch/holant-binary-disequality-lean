import Holant.Network
import Holant.BoundaryAction

/-!
Full open-gadget half-edge semantics from the revised manuscript. An exposed port
may be an unpaired ordinary vertex port or a paired free stub. The raw table and
boundary-corrected tensor are deliberately different definitions.
-/

namespace Holant

abbrev OpenPorts (vertices : ℕ) (arity : Fin vertices → ℕ) (free : ℕ) :=
  (Σ v : Fin vertices, Fin (arity v)) ⊕ Fin free

/-- Finite half-edge incidence, with all pairing and boundary obligations explicit. -/
structure OpenNetworkShape (n : ℕ) where
  vertices : ℕ
  arity : Fin vertices → ℕ
  free : ℕ
  edges : ℕ
  boundary : Fin n ↪ OpenPorts vertices arity free
  ends : (Fin edges × Bool) ↪ OpenPorts vertices arity free
  ordinary_boundary_iff_unpaired : ∀ p : Σ v : Fin vertices, Fin (arity v),
    (∃ j, boundary j = .inl p) ↔ ¬ ∃ q, ends q = .inl p
  freeBoundary : Fin free → Fin n
  free_boundary : ∀ f, boundary (freeBoundary f) = .inr f
  freeEdge : Fin free → Fin edges × Bool
  free_paired : ∀ f, ends (freeEdge f) = .inr f

namespace OpenNetworkShape

variable {n : ℕ}

theorem edge_endpoints_distinct (s : OpenNetworkShape n) (e : Fin s.edges) :
    s.ends (e, false) ≠ s.ends (e, true) := by
  intro h
  have h' := s.ends.injective h
  cases h'

theorem ordinary_boundary_not_paired (s : OpenNetworkShape n)
    (p : Σ v : Fin s.vertices, Fin (s.arity v))
    (j : Fin n) (h : s.boundary j = .inl p) : ¬ ∃ q, s.ends q = .inl p :=
  (s.ordinary_boundary_iff_unpaired p).mp ⟨j, h⟩

theorem freeBoundary_injective (s : OpenNetworkShape n) :
    Function.Injective s.freeBoundary := by
  intro a b h
  have h' := congrArg s.boundary h
  rw [s.free_boundary, s.free_boundary] at h'
  exact Sum.inr.inj h'

theorem freeEdge_injective (s : OpenNetworkShape n) : Function.Injective s.freeEdge := by
  intro a b h
  have h' := congrArg s.ends h
  rw [s.free_paired, s.free_paired] at h'
  exact Sum.inr.inj h'

end OpenNetworkShape

/-- Only the two involutive kernels allowed by the paper's baseline bookkeeping model. -/
inductive EdgeKind where
  | equality
  | disequality
  deriving DecidableEq

namespace EdgeKind

def value {K : Type*} [Semiring K] : EdgeKind → Bool → Bool → K
  | .equality => Signature.equality
  | .disequality => Signature.disequality

end EdgeKind

/-- Labelled open network. Structural edge boxes contribute no vertex factor. -/
structure OpenNetwork (K : Type*) (n : ℕ) where
  shape : OpenNetworkShape n
  vertex : (v : Fin shape.vertices) → Signature K (shape.arity v)
  edge : Fin shape.edges → EdgeKind

namespace OpenNetwork

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- Product of genuine vertex factors and exactly one kernel factor per wire pair. -/
def weight (N : OpenNetwork K n) (z : OpenPorts N.shape.vertices N.shape.arity N.shape.free → Bool) : K :=
  (∏ v : Fin N.shape.vertices, N.vertex v (fun i => z (.inl ⟨v, i⟩))) *
  ∏ e : Fin N.shape.edges,
    (N.edge e).value (z (N.shape.ends (e, false))) (z (N.shape.ends (e, true)))

/-- Sum all half-edge assignments that agree with the prescribed boundary word. -/
def raw (N : OpenNetwork K n) : Signature K n :=
  fun x => ∑ z : OpenPorts N.shape.vertices N.shape.arity N.shape.free → Bool,
    if ∀ j, z (N.shape.boundary j) = x j then N.weight z else 0

/-- Free boundary endpoints carry their wire kernel action; ordinary ports carry identity. -/
def boundaryKernel (N : OpenNetwork K n) (j : Fin n) : Bool → Bool → K :=
  match N.shape.boundary j with
  | .inl _ => Signature.equality
  | .inr f => (N.edge (N.shape.freeEdge f).1).value

/-- The boundary tensor used for gadget replacement in the manuscript. -/
def tensor (N : OpenNetwork K n) : Signature K n :=
  Signature.coordinateAction N.boundaryKernel N.raw

/-- When every boundary port is ordinary, the boundary correction is identity. -/
theorem tensor_eq_raw_of_ordinary (N : OpenNetwork K n)
    (h : ∀ j, ∃ p, N.shape.boundary j = .inl p) : N.tensor = N.raw := by
  have hk : N.boundaryKernel = fun _ => Signature.equality := by
    funext j
    obtain ⟨p, hp⟩ := h j
    simp [boundaryKernel, hp]
  simp [tensor, hk]

/-- Closed networks have no boundary-coordinate correction. -/
theorem tensor_eq_raw_closed (N : OpenNetwork K 0) : N.tensor = N.raw :=
  tensor_eq_raw_of_ordinary N (fun j => Fin.elim0 j)

end OpenNetwork
end Holant
