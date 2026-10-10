import Holant.OpenNetworkComposition.DisjointTensorShape
import Holant.OpenNetworkComposition.BoundaryKinds
import Holant.OpenNetworkComposition.BoundarySums
import Holant.OrderedTensor

/-! Exact raw and corrected tensor products for disjoint full open gadgets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.DisjointTensor
variable {K VL VR FL FR EL ER : Type*} {m n : ℕ}
variable (L : FiniteNetwork K VL FL EL m) (R : FiniteNetwork K VR FR ER n)

def network : FiniteNetwork K (VL⊕VR) (FL⊕FR) (EL⊕ER) (m+n) where
  shape := shape L.shape R.shape
  vertex
    | .inl v => L.vertex v
    | .inr v => R.vertex v
  edge := Sum.elim L.edge R.edge

def joinedAssignment (zL : Ports VL FL L.shape.arity → Bool) (zR : Ports VR FR R.shape.arity → Bool) :
    Ports (VL⊕VR) (FL⊕FR) (SumArity L.shape.arity R.shape.arity) → Bool :=
  fun p => Sum.elim zL zR (portSum L.shape.arity R.shape.arity p)

def assignmentEquiv :
    (Ports (VL⊕VR) (FL⊕FR) (SumArity L.shape.arity R.shape.arity) → Bool) ≃
      ((Ports VL FL L.shape.arity → Bool) × (Ports VR FR R.shape.arity → Bool)) :=
  (Equiv.arrowCongr (portSum L.shape.arity R.shape.arity) (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] theorem joined_left (zL : Ports VL FL L.shape.arity → Bool)
    (zR : Ports VR FR R.shape.arity → Bool) (p : Ports VL FL L.shape.arity) :
    joinedAssignment L R zL zR (leftPort L.shape.arity R.shape.arity p)=zL p := by
  simp [joinedAssignment]
@[simp] theorem joined_right (zL : Ports VL FL L.shape.arity → Bool)
    (zR : Ports VR FR R.shape.arity → Bool) (p : Ports VR FR R.shape.arity) :
    joinedAssignment L R zL zR (rightPort L.shape.arity R.shape.arity p)=zR p := by
  simp [joinedAssignment]

@[simp] theorem network_boundary_left (j : Fin m) :
    (network L R).shape.boundary (Fin.castAdd n j)=leftPort L.shape.arity R.shape.arity (L.shape.boundary j) :=
  boundary_left L.shape R.shape j
@[simp] theorem network_boundary_right (j : Fin n) :
    (network L R).shape.boundary (Fin.natAdd m j)=rightPort L.shape.arity R.shape.arity (R.shape.boundary j) :=
  boundary_right L.shape R.shape j

theorem joined_boundary_iff (zL : Ports VL FL L.shape.arity → Bool)
    (zR : Ports VR FR R.shape.arity → Bool) (x : Fin (m+n) → Bool) :
    (∀j,joinedAssignment L R zL zR ((network L R).shape.boundary j)=x j) ↔
      (∀j,zL (L.shape.boundary j)=x (Fin.castAdd n j)) ∧
      (∀j,zR (R.shape.boundary j)=x (Fin.natAdd m j)) := by
  constructor
  · intro h
    constructor
    · intro j
      simpa using h (Fin.castAdd n j)
    · intro j
      simpa using h (Fin.natAdd m j)
  · rintro ⟨hl,hr⟩ j
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    cases j with
    | inl j => simpa using hl j
    | inr j => simpa using hr j

theorem network_edges (W : EdgeKind) (hL : ∀e,L.edge e=W) (hR : ∀e,R.edge e=W) :
    ∀e,(network L R).edge e=W := by
  rintro (e|e)
  · exact hL e
  · exact hR e

variable [Fintype VL] [Fintype VR] [Fintype FL] [Fintype FR] [Fintype EL] [Fintype ER] [CommSemiring K]

theorem network_weight (zL : Ports VL FL L.shape.arity → Bool) (zR : Ports VR FR R.shape.arity → Bool) :
    (network L R).weight (joinedAssignment L R zL zR)=L.weight zL*R.weight zR := by
  have hend (e : (EL⊕ER)×Bool) : (network L R).shape.ends e=ends L.shape R.shape e := rfl
  unfold FiniteNetwork.weight
  simp only [hend,Fintype.prod_sum_type,ends_left,ends_right,joined_left,joined_right]
  change ((∏v,L.vertex v (fun k => zL (.inl ⟨v,k⟩))) * (∏v,R.vertex v (fun k => zR (.inl ⟨v,k⟩)))) *
    ((∏e,(L.edge e).value (zL (L.shape.ends (e,false))) (zL (L.shape.ends (e,true)))) *
      (∏e,(R.edge e).value (zR (R.shape.ends (e,false))) (zR (R.shape.ends (e,true)))))=_
  ac_rfl

theorem network_raw : (network L R).raw=Signature.tensor L.raw R.raw := by
  funext x
  let W := fun z : Ports (VL⊕VR) (FL⊕FR) (SumArity L.shape.arity R.shape.arity) → Bool =>
    if ∀j,z ((network L R).shape.boundary j)=x j then (network L R).weight z else 0
  have hraw : (network L R).raw x=∑z,W z := by
    unfold FiniteNetwork.raw
    apply sum_instances
    intro z
    rfl
  rw [hraw,←(assignmentEquiv L R).symm.sum_comp W,Fintype.sum_prod_type,Signature.tensor_apply]
  unfold FiniteNetwork.raw
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  apply sum_instances
  intro zL
  apply sum_instances
  intro zR
  change (if ∀j,joinedAssignment L R zL zR ((network L R).shape.boundary j)=x j then
    (network L R).weight (joinedAssignment L R zL zR) else 0)=_
  simp only [joined_boundary_iff,network_weight]
  by_cases hl : ∀j,zL (L.shape.boundary j)=x (Fin.castAdd n j)
  · by_cases hr : ∀j,zR (R.shape.boundary j)=x (Fin.natAdd m j) <;> simp [hl,hr]
  · simp [hl]

theorem network_flip_left (x : Fin (m+n) → Bool) :
    (fun j => (network L R).boundaryFlip x (Fin.castAdd n j))=
      L.boundaryFlip (fun j => x (Fin.castAdd n j)) := by
  funext j
  simp only [boundaryFlip_portFlip,network_boundary_left,portFlip_left]

theorem network_flip_right (x : Fin (m+n) → Bool) :
    (fun j => (network L R).boundaryFlip x (Fin.natAdd m j))=
      R.boundaryFlip (fun j => x (Fin.natAdd m j)) := by
  funext j
  simp only [boundaryFlip_portFlip,network_boundary_right,portFlip_right]

end Holant.OpenNetworkComposition.DisjointTensor

namespace Holant.OpenNetworkComposition.FiniteNetwork
variable {K V F E : Type*} {n : ℕ}
variable [Fintype V] [Fintype F] [Fintype E] [CommSemiring K]

theorem tensor_eq_raw_equality (N : FiniteNetwork K V F E n) (he : ∀e,N.edge e=.equality) :
    N.tensor=N.raw := by
  have hk : N.boundaryKernel=fun _ => Signature.equality := by
    funext j
    cases hj : N.shape.boundary j <;> simp [boundaryKernel,hj,he,EdgeKind.value]
  simp [tensor,hk]

end Holant.OpenNetworkComposition.FiniteNetwork

namespace Holant.OpenNetworkComposition.DisjointTensor
variable {K VL VR FL FR EL ER : Type*} {m n : ℕ}
variable [Fintype VL] [Fintype VR] [Fintype FL] [Fintype FR] [Fintype EL] [Fintype ER] [CommSemiring K]

/-- Either native kernel is preserved, including free/free edge-box components. -/
theorem network_tensor (L : FiniteNetwork K VL FL EL m) (R : FiniteNetwork K VR FR ER n)
    (W : EdgeKind) (hL : ∀e,L.edge e=W) (hR : ∀e,R.edge e=W) :
    (network L R).tensor=Signature.tensor L.tensor R.tensor := by
  cases W with
  | equality =>
    rw [FiniteNetwork.tensor_eq_raw_equality _ (network_edges L R _ hL hR),
      network_raw,FiniteNetwork.tensor_eq_raw_equality L hL,FiniteNetwork.tensor_eq_raw_equality R hR]
  | disequality =>
    funext x
    rw [FiniteNetwork.tensor_eq_raw_boundaryFlip _ (network_edges L R _ hL hR),network_raw]
    simp only [Signature.tensor_apply,network_flip_left,network_flip_right,
      FiniteNetwork.tensor_eq_raw_boundaryFlip L hL,FiniteNetwork.tensor_eq_raw_boundaryFlip R hR]

end Holant.OpenNetworkComposition.DisjointTensor
