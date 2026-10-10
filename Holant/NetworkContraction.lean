import Holant.Network
import Mathlib.Data.Fintype.Prod

/-!
# Closing two ports of an actual graph

The first two ordinary boundary occurrences become the independently oriented
ends of one new edge. All vertices, their labels and local port orders, old edges,
and remaining boundary order are preserved. The two occurrences may belong to
the same vertex, so the constructor permits genuine self-loops. The denotation
is exactly bilinear contraction, including asymmetric kernels and closed output.
-/

namespace Holant.Network

variable {K : Type*} {n : ℕ}

/-- An ordinary-boundary corolla: one supplied tensor, all its ports exposed in
order, and no internal edge. Nullary tensors remain one actual vertex. -/
def corolla (f : Signature K n) : Network K n where
  shape := {
    vertices := 1
    arity := fun _ => n
    edges := 0
    ports := {
      toFun p := .inl p.2
      invFun q := Sum.elim (fun i => ⟨0, i⟩) (fun q => Fin.elim0 q.1) q
      left_inv := by rintro ⟨v, i⟩; have hv : v = 0 := Subsingleton.elim _ _; subst v; rfl
      right_inv := by intro q; cases q with
        | inl i => rfl
        | inr q => exact Fin.elim0 q.1 } }
  vertex := fun _ => f
  edge := fun e => Fin.elim0 e

/-- Reclassify the first two boundary occurrences as the new edge's false/true
ends; shift old edge indices by one and keep the remaining boundary order. -/
def contractPorts (m n : ℕ) :
    (Fin (n + 2) ⊕ (Fin m × Bool)) ≃ (Fin n ⊕ (Fin (m + 1) × Bool)) where
  toFun
    | .inl i => Fin.cases (.inr (0, false))
        (fun j => Fin.cases (.inr (0, true)) Sum.inl j) i
    | .inr (e, b) => .inr (e.succ, b)
  invFun
    | .inl i => .inl i.succ.succ
    | .inr (e, b) => Fin.cases
        (if b then .inl 1 else .inl 0) (fun j => .inr (j, b)) e
  left_inv := by
    intro p
    cases p with
    | inl i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · rfl
    | inr q => rfl
  right_inv := by
    intro p
    cases p with
    | inl i => rfl
    | inr q =>
      rcases q with ⟨e, b⟩
      refine Fin.cases ?_ (fun j => ?_) e
      · cases b <;> rfl
      · rfl

/-- Add an oriented internal edge at two distinct ordinary boundary occurrences.
No vertices are inserted, deleted, merged, relabelled, or rescaled. -/
def contract (N : Network K (n + 2)) (E : Bool → Bool → K) : Network K n where
  shape := {
    vertices := N.shape.vertices
    arity := N.shape.arity
    edges := N.shape.edges + 1
    ports := N.shape.ports.trans (contractPorts N.shape.edges n) }
  vertex := N.vertex
  edge := Fin.cons E N.edge

@[simp] theorem contract_vertices (N : Network K (n + 2)) (E : Bool → Bool → K) :
    (N.contract E).shape.vertices = N.shape.vertices := rfl

@[simp] theorem contract_edges (N : Network K (n + 2)) (E : Bool → Bool → K) :
    (N.contract E).shape.edges = N.shape.edges + 1 := rfl

@[simp] theorem contract_new_edge (N : Network K (n + 2)) (E : Bool → Bool → K) :
    (N.contract E).edge (0 : Fin (N.shape.edges + 1)) = E := rfl

@[simp] theorem contract_old_edge (N : Network K (n + 2)) (E : Bool → Bool → K)
    (e : Fin N.shape.edges) : (N.contract E).edge e.succ = N.edge e := rfl

@[simp] theorem contract_remaining_boundary (N : Network K (n + 2))
    (E : Bool → Bool → K) (i : Fin n) :
    (N.contract E).shape.ports.symm (.inl i) = N.shape.ports.symm (.inl i.succ.succ) := rfl

@[simp] theorem contract_first_endpoint (N : Network K (n + 2))
    (E : Bool → Bool → K) :
    (N.contract E).shape.ports.symm (.inr ((0 : Fin (N.shape.edges + 1)), false)) = N.shape.ports.symm (.inl 0) := rfl

@[simp] theorem contract_second_endpoint (N : Network K (n + 2))
    (E : Bool → Bool → K) :
    (N.contract E).shape.ports.symm (.inr ((0 : Fin (N.shape.edges + 1)), true)) = N.shape.ports.symm (.inl 1) := rfl

@[simp] theorem contract_old_endpoint (N : Network K (n + 2))
    (E : Bool → Bool → K) (e : Fin N.shape.edges) (b : Bool) :
    (N.contract E).shape.ports.symm (.inr (e.succ, b)) =
      N.shape.ports.symm (.inr (e, b)) := rfl

/-- All original internal bits remain independent of the two new endpoint bits. -/
def contractAssignments (m : ℕ) :
    ((Fin (m + 1) × Bool) → Bool) ≃
      (Bool × Bool × ((Fin m × Bool) → Bool)) where
  toFun z := (z (0, false), z (0, true), fun q => z (q.1.succ, q.2))
  invFun p q := Fin.cases (if q.2 then p.2.1 else p.1) (fun e => p.2.2 (e, q.2)) q.1
  left_inv := by
    intro z
    funext q
    rcases q with ⟨e, b⟩
    refine Fin.cases ?_ (fun j => ?_) e
    · cases b <;> rfl
    · rfl
  right_inv := by intro p; rfl

variable [CommSemiring K]

@[simp] theorem denote_corolla (f : Signature K n) : (corolla f).denote = f := by
  funext x
  dsimp [denote, corolla, NetworkShape.assignment]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Graph-level self-gluing is exactly the specified ordered bilinear tensor
contraction. In particular, no extra loop or normalization scalar is dropped. -/
theorem denote_contract (N : Network K (n + 2)) (E : Bool → Bool → K) :
    (N.contract E).denote = Signature.contract E N.denote := by
  classical
  funext x
  unfold denote Signature.contract
  change (∑ z : (Fin (N.shape.edges + 1) × Bool) → Bool,
    (∏ v, N.vertex v ((N.contract E).shape.assignment x z v)) *
      ∏ e : Fin (N.shape.edges + 1), (N.contract E).edge e (z (e, false)) (z (e, true))) = _
  rw [← (contractAssignments N.shape.edges).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro z _
  have ha : (N.contract E).shape.assignment x
      ((contractAssignments N.shape.edges).symm (a, b, z)) =
      N.shape.assignment (Fin.cons a (Fin.cons b x)) z := by
    funext v i
    dsimp [NetworkShape.assignment, contract]
    generalize hp : N.shape.ports ⟨v, i⟩ = p
    cases p with
    | inl j =>
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun l => ?_) k
        · rfl
        · rfl
    | inr q => rfl
  rw [ha]
  simp only [contract, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  dsimp [contractAssignments]
  ac_rfl

/-- Equality sums the two equal-bit boundary conditions exactly. -/
theorem denote_contract_equality (N : Network K (n + 2)) (x : Fin n → Bool) :
    (N.contract Signature.equality).denote x =
      N.denote (Fin.cons false (Fin.cons false x)) +
        N.denote (Fin.cons true (Fin.cons true x)) := by
  rw [denote_contract, Signature.contract_equality]

/-- A native X edge sums the two opposite-bit boundary conditions exactly. -/
theorem denote_contract_disequality (N : Network K (n + 2)) (x : Fin n → Bool) :
    (N.contract Signature.disequality).denote x =
      N.denote (Fin.cons false (Fin.cons true x)) +
        N.denote (Fin.cons true (Fin.cons false x)) := by
  rw [denote_contract, Signature.contract_disequality]

end Holant.Network
