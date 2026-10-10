import Holant.Tensor

/-!
Finite ordered-port networks with explicit occurrences at both ends of each edge.
The port bijection permits loops and parallel edges and prohibits dangling,
duplicated, or missing occurrences. Native edges carry their own tensors.
-/

namespace Holant

/-- The incidence data for a network with `n` ordered external ports. -/
structure NetworkShape (n : ℕ) where
  vertices : ℕ
  arity : Fin vertices → ℕ
  edges : ℕ
  ports : (Σ v : Fin vertices, Fin (arity v)) ≃ (Fin n ⊕ (Fin edges × Bool))

namespace NetworkShape

variable {n : ℕ}

/-- Combine fixed boundary bits with the independent bits at internal edge ends. -/
def assignment (s : NetworkShape n) (x : Fin n → Bool)
    (z : (Fin s.edges × Bool) → Bool) (v : Fin s.vertices) : Fin (s.arity v) → Bool :=
  fun i => Sum.elim x z (s.ports ⟨v, i⟩)

/-- A loop has two distinct port occurrences even if its endpoints share a vertex. -/
theorem edge_endpoints_distinct (s : NetworkShape n) (e : Fin s.edges) :
    s.ports.symm (.inr (e, false)) ≠ s.ports.symm (.inr (e, true)) := by
  intro h
  have h' := s.ports.symm.injective h
  cases h'

/-- The empty closed network has neither vertices nor edges. -/
def empty : NetworkShape 0 where
  vertices := 0
  arity := Fin.elim0
  edges := 0
  ports := {
    toFun := fun p => Fin.elim0 p.1
    invFun := fun p => Sum.elim Fin.elim0 (fun q => Fin.elim0 q.1) p
    left_inv := fun p => Fin.elim0 p.1
    right_inv := fun p => by
      cases p with
      | inl i => exact Fin.elim0 i
      | inr q => exact Fin.elim0 q.1 }

end NetworkShape

/-- A network's vertex and edge labels. Edge tensors are not identified with vertex labels. -/
structure Network (K : Type*) (n : ℕ) where
  shape : NetworkShape n
  vertex : (v : Fin shape.vertices) → Signature K (shape.arity v)
  edge : Fin shape.edges → Bool → Bool → K

namespace Network

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- The actual finite sum of products defining an open network's signature. -/
def denote (N : Network K n) : Signature K n :=
  fun x => ∑ z : (Fin N.shape.edges × Bool) → Bool,
    (∏ v : Fin N.shape.vertices, N.vertex v (N.shape.assignment x z v)) *
    ∏ e : Fin N.shape.edges, N.edge e (z (e, false)) (z (e, true))

/-- Empty components contribute exactly the multiplicative identity. -/
def empty : Network K 0 where
  shape := NetworkShape.empty
  vertex := fun v => Fin.elim0 v
  edge := fun e => Fin.elim0 e

@[simp] theorem denote_empty (x : Fin 0 → Bool) : (empty : Network K 0).denote x = 1 := by
  dsimp [denote, empty, NetworkShape.empty]
  simp

/-- Replacing labels by pointwise equal labels preserves the entire open signature. -/
theorem denote_congr (s : NetworkShape n)
    (f g : (v : Fin s.vertices) → Signature K (s.arity v))
    (E D : Fin s.edges → Bool → Bool → K)
    (hf : ∀ v x, f v x = g v x) (hE : ∀ e a b, E e a b = D e a b) :
    (Network.mk s f E).denote = (Network.mk s g D).denote := by
  have hfg : f = g := funext fun v => funext (hf v)
  have hED : E = D := funext fun e => funext fun a => funext (hE e a)
  subst g
  subst D
  rfl

end Network
end Holant
