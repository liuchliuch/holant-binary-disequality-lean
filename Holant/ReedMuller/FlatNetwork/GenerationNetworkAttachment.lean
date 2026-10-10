import Holant.NetworkTensor
import Holant.NetworkContraction
import Holant.OrdinaryNetwork

/-! Actual partial-port attachment used by the converse circuit construction.
An ordered `2r`-port box replaces `r` chosen ordinary boundary occurrences,
retains every old vertex/edge, and adds exactly one vertex and `r` I edges. -/
namespace Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

namespace GenerationNetwork
variable {K : Type*} {n r m : ℕ}

/-- A purely incidence-level replacement: the old selected boundary ports
become false endpoints, box inputs become true endpoints, and box outputs
become the new selected boundary ports. -/
def attachmentPorts (E : Type*) (r m : ℕ) :
    (((Fin r ⊕ Fin m) ⊕ (E × Bool)) ⊕ (Fin r ⊕ Fin r)) ≃
      ((Fin r ⊕ Fin m) ⊕ ((E ⊕ Fin r) × Bool)) where
  toFun
    | .inl (.inl (.inl i)) => .inr (.inr i, false)
    | .inl (.inl (.inr j)) => .inl (.inr j)
    | .inl (.inr (e,b)) => .inr (.inl e,b)
    | .inr (.inl i) => .inr (.inr i,true)
    | .inr (.inr i) => .inl (.inl i)
  invFun
    | .inl (.inl i) => .inr (.inr i)
    | .inl (.inr j) => .inl (.inl (.inr j))
    | .inr (.inl e,b) => .inl (.inr (e,b))
    | .inr (.inr i,false) => .inl (.inl (.inl i))
    | .inr (.inr i,true) => .inr (.inl i)
  left_inv := by
    rintro (((i | j) | ⟨e,b⟩) | (i | i)) <;> rfl
  right_inv := by
    rintro ((i | j) | ⟨e | i,b⟩)
    · rfl
    · rfl
    · rfl
    · cases b <;> rfl

def attachmentVertexPorts (N : Network K n) (r : ℕ) :
    (Σ v : Fin N.shape.vertices ⊕ Unit, Fin (Sum.elim N.shape.arity (fun _ => r+r) v)) ≃
      ((Σ v : Fin N.shape.vertices, Fin (N.shape.arity v)) ⊕ Fin (r+r)) where
  toFun
    | ⟨.inl v,i⟩ => .inl ⟨v,i⟩
    | ⟨.inr _,i⟩ => .inr i
  invFun
    | .inl ⟨v,i⟩ => ⟨.inl v,i⟩
    | .inr i => ⟨.inr (),i⟩
  left_inv := by rintro ⟨v | ⟨⟩,i⟩ <;> rfl
  right_inv := by rintro (⟨v,i⟩ | i) <;> rfl

/-- The finite-index graph before enumeration. `selection` orders the selected
and retained old boundary ports; `boxOrder` orders the new input/output ports. -/
def attachFinite [CommSemiring K] (N : Network K n) (B : Signature K (r+r))
    (selection : Fin n ≃ Fin r ⊕ Fin m) (boxOrder : Fin (r+r) ≃ Fin r ⊕ Fin r) :
    FiniteNetwork K (Fin N.shape.vertices ⊕ Unit) (Fin N.shape.edges ⊕ Fin r) n where
  arity := Sum.elim N.shape.arity (fun _ => r+r)
  ports := (attachmentVertexPorts N r).trans
    ((Equiv.sumCongr (N.shape.ports.trans
      (Equiv.sumCongr selection (Equiv.refl _))) boxOrder).trans
      ((attachmentPorts (Fin N.shape.edges) r m).trans
        (Equiv.sumCongr selection.symm (Equiv.refl _))))
  vertex := fun v => match v with
    | .inl v => N.vertex v
    | .inr _ => B
  edge := Sum.elim N.edge (fun _ => Signature.equality)

def attach [CommSemiring K] (N : Network K n) (B : Signature K (r+r))
    (selection : Fin n ≃ Fin r ⊕ Fin m) (boxOrder : Fin (r+r) ≃ Fin r ⊕ Fin r) :
    Network K n := (attachFinite N B selection boxOrder).toNetwork

@[simp] theorem attach_vertices [CommSemiring K] (N : Network K n) (B : Signature K (r+r))
    (selection : Fin n ≃ Fin r ⊕ Fin m) (boxOrder : Fin (r+r) ≃ Fin r ⊕ Fin r) :
    (attach N B selection boxOrder).shape.vertices = N.shape.vertices + 1 := by
  simp [attach, FiniteNetwork.toNetwork]

@[simp] theorem attach_edges [CommSemiring K] (N : Network K n) (B : Signature K (r+r))
    (selection : Fin n ≃ Fin r ⊕ Fin m) (boxOrder : Fin (r+r) ≃ Fin r ⊕ Fin r) :
    (attach N B selection boxOrder).shape.edges = N.shape.edges + r := by
  simp [attach, FiniteNetwork.toNetwork]

/-- Replace just the selected bits of a boundary word by the input bits. -/
def inputBoundary (selection : Fin n ≃ Fin r ⊕ Fin m) (a : Fin r → Bool)
    (x : Fin n → Bool) : Fin n → Bool :=
  fun i => Sum.elim a (fun j => x (selection.symm (.inr j))) (selection i)

def boxBoundary (selection : Fin n ≃ Fin r ⊕ Fin m)
    (boxOrder : Fin (r+r) ≃ Fin r ⊕ Fin r) (a : Fin r → Bool)
    (x : Fin n → Bool) : Fin (r+r) → Bool :=
  fun i => Sum.elim a (fun j => x (selection.symm (.inl j))) (boxOrder i)

def attachmentAssignments (E : Type*) (r : ℕ) :
    (((E ⊕ Fin r) × Bool) → Bool) ≃
      (((E × Bool) → Bool) × ((Fin r → Bool) × (Fin r → Bool))) :=
  (Network.tensorAssignments E (Fin r)).trans
    (Equiv.prodCongr (Equiv.refl _) (halfEdgeAssignmentsEquiv r))

private theorem old_assignment [CommSemiring K] (N : Network K n) (B : Signature K (r+r))
    (selection : Fin n ≃ Fin r ⊕ Fin m) (boxOrder : Fin (r+r) ≃ Fin r ⊕ Fin r)
    (x : Fin n → Bool) (z : (Fin N.shape.edges × Bool) → Bool) (a b : Fin r → Bool)
    (v : Fin N.shape.vertices) :
    (fun i => Sum.elim x ((attachmentAssignments (Fin N.shape.edges) r).symm (z,a,b))
      ((attachFinite N B selection boxOrder).ports ⟨.inl v,i⟩)) =
      N.shape.assignment (inputBoundary selection a x) z v := by
  funext i
  dsimp [attachFinite, attachmentVertexPorts, NetworkShape.assignment]
  generalize hp : N.shape.ports ⟨v,i⟩ = p
  cases p with
  | inl j =>
    dsimp [inputBoundary]
    generalize hj : selection j = q
    cases q <;> simp [Equiv.sumCongr_apply, Equiv.trans_apply, hp, hj, attachmentPorts,
      attachmentAssignments, Network.tensorAssignments, halfEdgeAssignmentsEquiv]
  | inr q =>
    rcases q with ⟨e,c⟩
    simp [Equiv.sumCongr_apply, Equiv.trans_apply, hp, attachmentPorts,
      attachmentAssignments, Network.tensorAssignments, halfEdgeAssignmentsEquiv]

private theorem box_assignment [CommSemiring K] (N : Network K n) (B : Signature K (r+r))
    (selection : Fin n ≃ Fin r ⊕ Fin m) (boxOrder : Fin (r+r) ≃ Fin r ⊕ Fin r)
    (x : Fin n → Bool) (z : (Fin N.shape.edges × Bool) → Bool) (a b : Fin r → Bool) :
    (fun i => Sum.elim x ((attachmentAssignments (Fin N.shape.edges) r).symm (z,a,b))
      ((attachFinite N B selection boxOrder).ports ⟨.inr (),i⟩)) =
      boxBoundary selection boxOrder b x := by
  funext i
  dsimp [attachFinite, attachmentVertexPorts, boxBoundary]
  generalize hi : boxOrder i = q
  cases q <;> simp [Equiv.sumCongr_apply, Equiv.trans_apply, hi, attachmentPorts,
    attachmentAssignments, Network.tensorAssignments, halfEdgeAssignmentsEquiv]

/-- Exact graph-level sum identity for partial attachment. Both endpoint bits
of each equality edge are summed before equality collapses them, so this keeps
all original internal assignments and introduces no hidden normalization. -/
theorem denote_attach [CommSemiring K] (N : Network K n) (B : Signature K (r+r))
    (selection : Fin n ≃ Fin r ⊕ Fin m) (boxOrder : Fin (r+r) ≃ Fin r ⊕ Fin r)
    (x : Fin n → Bool) :
    (attach N B selection boxOrder).denote x =
      ∑ a : Fin r → Bool, N.denote (inputBoundary selection a x) *
        B (boxBoundary selection boxOrder a x) := by
  let : DecidableEq (Fin N.shape.edges ⊕ Fin r) := Classical.decEq _
  rw [attach, FiniteNetwork.denote_toNetwork]
  unfold FiniteNetwork.denote
  change (∑ z : ((Fin N.shape.edges ⊕ Fin r) × Bool) → Bool,
    (∏ v, (attachFinite N B selection boxOrder).vertex v (fun i =>
      Sum.elim x z ((attachFinite N B selection boxOrder).ports ⟨v,i⟩))) *
      ∏ e, (attachFinite N B selection boxOrder).edge e (z (e,false)) (z (e,true))) = _
  rw [← (attachmentAssignments (Fin N.shape.edges) r).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_sum_type, Fintype.prod_unique]
  simp only [old_assignment, box_assignment]
  have hedge (z : (Fin N.shape.edges × Bool) → Bool) (a b : Fin r → Bool) :
      (∏ e : Fin N.shape.edges, (attachFinite N B selection boxOrder).edge (.inl e)
        ((attachmentAssignments (Fin N.shape.edges) r).symm (z,a,b) (.inl e,false))
        ((attachmentAssignments (Fin N.shape.edges) r).symm (z,a,b) (.inl e,true))) *
      (∏ e : Fin r, (attachFinite N B selection boxOrder).edge (.inr e)
        ((attachmentAssignments (Fin N.shape.edges) r).symm (z,a,b) (.inr e,false))
        ((attachmentAssignments (Fin N.shape.edges) r).symm (z,a,b) (.inr e,true))) =
      (∏ e, N.edge e (z (e,false)) (z (e,true))) * (if a=b then 1 else 0) := by
    change (∏ e, N.edge e (z (e,false)) (z (e,true))) *
      (∏ i, Signature.equality (a i) (b i)) = _
    rw [Signature.prod_equality]
  simp only [hedge]
  change (∑ z : (Fin N.shape.edges × Bool) → Bool, ∑ a : Fin r → Bool, ∑ b : Fin r → Bool,
    ((∏ v, N.vertex v (N.shape.assignment (inputBoundary selection a x) z v)) *
      B (boxBoundary selection boxOrder b x)) *
      ((∏ e, N.edge e (z (e,false)) (z (e,true))) * (if a=b then 1 else 0))) = _
  simp only [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Network.denote, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  ac_rfl

end GenerationNetwork
end
end Holant.ReedMuller.FlatNetwork
