import Holant.Network
import Holant.BoundaryAction

/-!
Closed-network holographic invariance for the actual finite assignment denotation.
Every vertex is acted on by the inverse-column matrix, and every edge is pulled
back by the forward matrix. The incidence bijection, not a simplicity assumption,
is what makes the proof work; loops, parallel edges, and nullary vertices remain.
-/

namespace Holant

namespace NetworkShape

/-- In a closed shape every vertex port is exactly one internal edge occurrence. -/
def closedPorts (s : NetworkShape 0) :
    (Σ v : Fin s.vertices, Fin (s.arity v)) ≃ (Fin s.edges × Bool) :=
  s.ports.trans (Equiv.emptySum (Fin 0) (Fin s.edges × Bool))

@[simp] theorem assignment_closed (s : NetworkShape 0) (x : Fin 0 → Bool)
    (z : (Fin s.edges × Bool) → Bool) (v : Fin s.vertices) (i : Fin (s.arity v)) :
    s.assignment x z v i = z (s.closedPorts ⟨v, i⟩) := by
  dsimp [assignment, closedPorts]
  cases h : s.ports ⟨v, i⟩ with
  | inl a => exact Fin.elim0 a
  | inr q => rfl

/-- Assignment transport along the actual port bijection, followed by currying. -/
def closedAssignments (s : NetworkShape 0) :
    ((Fin s.edges × Bool) → Bool) ≃ ((v : Fin s.vertices) → Fin (s.arity v) → Bool) :=
  (Equiv.arrowCongr s.closedPorts.symm (Equiv.refl Bool)).trans
    (Equiv.piCurry fun (v : Fin s.vertices) (_ : Fin (s.arity v)) => Bool)

@[simp] theorem closedAssignments_apply (s : NetworkShape 0)
    (z : (Fin s.edges × Bool) → Bool) (v : Fin s.vertices) (i : Fin (s.arity v)) :
    s.closedAssignments z v i = z (s.closedPorts ⟨v, i⟩) := rfl

/-- Products over local ordered ports count every edge occurrence exactly once. -/
theorem prod_closedPorts {K : Type*} [CommMonoid K] (s : NetworkShape 0)
    (f : (Fin s.edges × Bool) → K) :
    (∏ v : Fin s.vertices, ∏ i : Fin (s.arity v), f (s.closedPorts ⟨v, i⟩)) =
      ∏ q : Fin s.edges × Bool, f q := by
  rw [← Fintype.prod_sigma (fun p => f (s.closedPorts p))]
  exact s.closedPorts.prod_comp f

end NetworkShape

namespace Network

variable {K : Type*} [CommSemiring K]

/-- The uniform column action is applied at every ordered slot of every vertex. -/
def holographicTransform (G : Network K 0) (M N : Kernel K) : Network K 0 where
  shape := G.shape
  vertex := fun v => Signature.coordinateAction (fun _ => N) (G.vertex v)
  edge := fun e => Kernel.pullback (G.edge e) M

/-- Expanding all vertex actions gives one sum over the network's edge occurrences. -/
theorem prod_vertex_action (s : NetworkShape 0)
    (f : (v : Fin s.vertices) → Signature K (s.arity v)) (N : Kernel K)
    (x : Fin 0 → Bool) (z : (Fin s.edges × Bool) → Bool) :
    (∏ v : Fin s.vertices,
      Signature.coordinateAction (fun _ => N) (f v) (s.assignment x z v)) =
    ∑ y : (Fin s.edges × Bool) → Bool,
      (∏ q : Fin s.edges × Bool, N (z q) (y q)) *
        ∏ v : Fin s.vertices, f v (s.assignment x y v) := by
  classical
  simp only [Signature.coordinateAction]
  rw [Fintype.prod_sum, ← s.closedAssignments.sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.prod_mul_distrib]
  congr 1
  · simp only [NetworkShape.assignment_closed, NetworkShape.closedAssignments_apply]
    exact s.prod_closedPorts (fun q => N (z q) (y q))
  · apply Finset.prod_congr rfl
    intro v _
    congr 1
    funext i
    simp

/-- Fubini for independent assignments to the two ordered occurrences of each edge. -/
theorem sum_halfEdge_products (m : ℕ) (f : Fin m → Bool → Bool → K) :
    (∑ z : (Fin m × Bool) → Bool,
      ∏ e : Fin m, f e (z (e, false)) (z (e, true))) =
    ∏ e : Fin m, ∑ a : Bool, ∑ b : Bool, f e a b := by
  classical
  rw [← (Equiv.curry (Fin m) Bool Bool).symm.sum_comp]
  change (∑ z : Fin m → Bool → Bool, ∏ e : Fin m, f e (z e false) (z e true)) = _
  rw [← Fintype.prod_sum (fun e (w : Bool → Bool) => f e (w false) (w true))]
  apply Finset.prod_congr rfl
  intro e _
  rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- Cancellation at an edge with both original endpoint bits held fixed. -/
theorem edge_holographic_cancel (E M N : Kernel K)
    (hMN : Kernel.mul M N = Signature.equality) (c d : Bool) :
    (∑ a : Bool, ∑ b : Bool,
      N a c * N b d * Kernel.pullback E M a b) = E c d := by
  have h := Kernel.connect_change_basis E M N hMN
    (fun a => Signature.equality a c) (fun b => Signature.equality b d)
  cases c <;> cases d <;>
    simpa [Kernel.act, Signature.connect, Signature.equality, mul_comm, mul_left_comm,
      mul_assoc] using h

/-- Independent local edge cancellations multiply to a cancellation of the full edge tensor. -/
theorem sum_edge_action (m : ℕ) (E : Fin m → Kernel K) (M N : Kernel K)
    (hMN : Kernel.mul M N = Signature.equality) (y : (Fin m × Bool) → Bool) :
    (∑ z : (Fin m × Bool) → Bool,
      (∏ q : Fin m × Bool, N (z q) (y q)) *
        ∏ e : Fin m, Kernel.pullback (E e) M (z (e, false)) (z (e, true))) =
    ∏ e : Fin m, E e (y (e, false)) (y (e, true)) := by
  simp only [Fintype.prod_prod_type, Fintype.prod_bool]
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_halfEdge_products m (fun e a b =>
    N b (y (e, true)) * N a (y (e, false)) * Kernel.pullback (E e) M a b)]
  apply Finset.prod_congr rfl
  intro e _
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    edge_holographic_cancel (E e) M N hMN (y (e, false)) (y (e, true))

set_option backward.isDefEq.respectTransparency false in
/-- Genuine closed-network holographic invariance, proved for `Network.denote`.
The sole inverse assumption has orientation `M N = I`, matching column actions.
No restrictions on loops, parallel edges, components, or vertex arities are used. -/
theorem denote_holographicTransform (G : Network K 0) (M N : Kernel K)
    (hMN : Kernel.mul M N = Signature.equality) :
    (holographicTransform G M N).denote = G.denote := by
  classical
  funext x
  simp only [denote, holographicTransform]
  simp_rw [prod_vertex_action]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (∏ v : Fin G.shape.vertices, G.vertex v (G.shape.assignment x y v)) *
        ∑ z : (Fin G.shape.edges × Bool) → Bool,
          (∏ q : Fin G.shape.edges × Bool, N (z q) (y q)) *
            ∏ e : Fin G.shape.edges,
              Kernel.pullback (G.edge e) M (z (e, false)) (z (e, true)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ac_rfl
    _ = _ := by rw [sum_edge_action G.shape.edges G.edge M N hMN]

end Network
end Holant
