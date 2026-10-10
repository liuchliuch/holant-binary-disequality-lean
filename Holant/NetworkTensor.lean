import Holant.NetworkGluing.Finite
import Holant.OrderedTensor
import Holant.NetworkAsGadget

/-!
# Tensoring actual ordered-port networks

Disjoint union retains every genuine vertex, loop and parallel edge. Its boundary
is the complete left boundary followed by the complete right boundary. The
finite-sum theorem is exact, including empty networks and nullary factors.
-/

namespace Holant.Network

variable {K : Type*} {m n : ℕ}

/-- Reclassify disjoint boundary and edge occurrences without identifying any. -/
def tensorPorts (EL ER : Type*) (m n : ℕ) :
    ((Fin m ⊕ (EL × Bool)) ⊕ (Fin n ⊕ (ER × Bool))) ≃
      (Fin (m + n) ⊕ ((EL ⊕ ER) × Bool)) :=
  (Equiv.sumSumSumComm _ _ _ _).trans
    (Equiv.sumCongr finSumFinEquiv (Equiv.sumProdDistrib EL ER Bool).symm)

/-- Disjoint union before finite enumeration. Every local port number is kept. -/
def tensorFinite (L : Network K m) (R : Network K n) :
    FiniteNetwork K (Fin L.shape.vertices ⊕ Fin R.shape.vertices)
      (Fin L.shape.edges ⊕ Fin R.shape.edges) (m + n) where
  arity := Sum.elim L.shape.arity R.shape.arity
  ports := (Equiv.sumSigmaDistrib (fun v => Fin (Sum.elim L.shape.arity R.shape.arity v))).trans
    ((Equiv.sumCongr L.shape.ports R.shape.ports).trans
      (tensorPorts _ _ m n))
  vertex := fun v => match v with
    | .inl v => L.vertex v
    | .inr v => R.vertex v
  edge := Sum.elim L.edge R.edge

/-- Actual graph disjoint union, with original-left-ports-first boundary order. -/
noncomputable def tensor (L : Network K m) (R : Network K n) : Network K (m + n) :=
  (tensorFinite L R).toNetwork

@[simp] theorem tensor_vertices (L : Network K m) (R : Network K n) :
    (L.tensor R).shape.vertices = L.shape.vertices + R.shape.vertices := by
  simp [tensor, FiniteNetwork.toNetwork]

@[simp] theorem tensor_edges (L : Network K m) (R : Network K n) :
    (L.tensor R).shape.edges = L.shape.edges + R.shape.edges := by
  simp [tensor, FiniteNetwork.toNetwork]

/-- A complete union assignment is precisely one independent assignment per side. -/
def tensorAssignments (EL ER : Type*) :
    (((EL ⊕ ER) × Bool) → Bool) ≃
      (((EL × Bool) → Bool) × ((ER × Bool) → Bool)) where
  toFun z := (fun q => z (.inl q.1, q.2), fun q => z (.inr q.1, q.2))
  invFun p q := match q.1 with
    | .inl e => p.1 (e, q.2)
    | .inr e => p.2 (e, q.2)
  left_inv z := by funext q; rcases q with ⟨e | e, b⟩ <;> rfl
  right_inv p := rfl

variable [CommSemiring K]

set_option backward.isDefEq.respectTransparency false in
/-- The actual graph assignment sum equals the ordered tensor product. -/
theorem denote_tensor (L : Network K m) (R : Network K n) :
    (L.tensor R).denote = Signature.tensor L.denote R.denote := by
  classical
  let : DecidableEq (Fin L.shape.edges ⊕ Fin R.shape.edges) := Classical.decEq _
  funext x
  rw [tensor, FiniteNetwork.denote_toNetwork]
  unfold FiniteNetwork.denote
  change (∑ z : ((Fin L.shape.edges ⊕ Fin R.shape.edges) × Bool) → Bool,
    (∏ v, (tensorFinite L R).vertex v (fun i => Sum.elim x z ((tensorFinite L R).ports ⟨v, i⟩))) *
      ∏ e, (tensorFinite L R).edge e (z (e, false)) (z (e, true))) = _
  rw [← (tensorAssignments (Fin L.shape.edges) (Fin R.shape.edges)).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Signature.tensor_apply, denote,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro zL _
  apply Finset.sum_congr rfl
  intro zR _
  dsimp only [tensorFinite]
  simp only [Fintype.prod_sum_type]
  have hl : (fun (v : Fin L.shape.vertices) (i : Fin (L.shape.arity v)) =>
      Sum.elim x ((tensorAssignments (Fin L.shape.edges) (Fin R.shape.edges)).symm (zL, zR))
        ((tensorFinite L R).ports ⟨.inl v, i⟩)) =
      L.shape.assignment (fun i => x (Fin.castAdd n i)) zL := by
    funext v i
    dsimp [tensorFinite, NetworkShape.assignment]
    change Sum.elim x _ (tensorPorts _ _ m n (.inl (L.shape.ports ⟨v, i⟩))) = _
    cases L.shape.ports ⟨v, i⟩ <;> rfl
  have hr : (fun (v : Fin R.shape.vertices) (i : Fin (R.shape.arity v)) =>
      Sum.elim x ((tensorAssignments (Fin L.shape.edges) (Fin R.shape.edges)).symm (zL, zR))
        ((tensorFinite L R).ports ⟨.inr v, i⟩)) =
      R.shape.assignment (fun i => x (Fin.natAdd m i)) zR := by
    funext v i
    dsimp [tensorFinite, NetworkShape.assignment]
    change Sum.elim x _ (tensorPorts _ _ m n (.inr (R.shape.ports ⟨v, i⟩))) = _
    cases R.shape.ports ⟨v, i⟩ <;> rfl
  dsimp [tensorAssignments]
  dsimp [tensorFinite, tensorAssignments] at hl hr
  simp only [congrFun₂ hl, congrFun₂ hr]
  ac_rfl

/-- The literal disjoint-union graph is an allowed gadget using exactly the
original resource families, with no new supplied signature. -/
theorem realizes_tensor (L : Network K m) (R : Network K n)
    (F : SignatureFamily K) (W : EdgeKind)
    (hL : ∀ v, (⟨L.shape.arity v, L.vertex v⟩ : AnySignature K) ∈ F)
    (hR : ∀ v, (⟨R.shape.arity v, R.vertex v⟩ : AnySignature K) ∈ F)
    (heL : ∀ e, L.edge e = W.value) (heR : ∀ e, R.edge e = W.value) :
    Gadget.Realizes F W (Signature.tensor L.denote R.denote) := by
  rw [← denote_tensor]
  apply Gadget.realizes_network
  · intro v
    change (⟨_, (tensorFinite L R).vertex
      ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)⟩ :
      AnySignature K) ∈ F
    cases (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
    | inl v => exact hL v
    | inr v => exact hR v
  · intro e
    change (tensorFinite L R).edge
      ((Fintype.equivFin (Fin L.shape.edges ⊕ Fin R.shape.edges)).symm e) = _
    cases (Fintype.equivFin (Fin L.shape.edges ⊕ Fin R.shape.edges)).symm e with
    | inl e => exact heL e
    | inr e => exact heR e

end Holant.Network
