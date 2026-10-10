import Holant.OpenNetworkComposition.OrdinarySemantics
import Holant.OpenNetworkComposition.BoundaryKinds

/-! Boundary-corrected native-X law for the ordinary/ordinary splice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.Ordinary
variable {K VL FL EL VR FR ER : Type*} {n : ℕ}
variable (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2) (i : Fin n)
    (pL : Σv,Fin (L.shape.arity v)) (pR : Σv,Fin (R.shape.arity v))
    (hL : L.shape.boundary i=.inl pL) (hR : R.shape.boundary 1=.inl pR)

theorem boundaryFlip_network_away (x : Fin n → Bool) (j : Fin n) (hj : j≠i) :
    (network L R i pL pR hL hR).boundaryFlip x j=L.boundaryFlip x j := by
  rw [boundaryFlip_portFlip,boundaryFlip_portFlip]
  change portFlip (if j=i then rightPort L.shape.arity R.shape.arity (R.shape.boundary 0)
    else leftPort L.shape.arity R.shape.arity (L.shape.boundary j)) (x j)=_
  rw [if_neg hj,portFlip_left]

theorem boundaryFlip_network_at (x : Fin n → Bool) :
    (network L R i pL pR hL hR).boundaryFlip x i=R.flipBit 0 (x i) := by
  rw [boundaryFlip_portFlip,flipBit_portFlip]
  change portFlip (if i=i then rightPort L.shape.arity R.shape.arity (R.shape.boundary 0)
    else leftPort L.shape.arity R.shape.arity (L.shape.boundary i)) (x i)=_
  rw [if_pos rfl,portFlip_right]

variable [Fintype VL] [Fintype FL] [Fintype EL] [Fintype VR] [Fintype FR] [Fintype ER] [CommSemiring K]

theorem network_tensor (eL : ∀e,L.edge e=.disequality) (eR : ∀e,R.edge e=.disequality) :
    (network L R i pL pR hL hR).tensor=spliceTensor L.tensor R.tensor i := by
  apply tensor_splice_of_raw L R (network L R i pL pR hL hR) i
    (boundaryFlip_network_away L R i pL pR hL hR) (boundaryFlip_network_at L R i pL pR hL hR)
    eL eR (network_edges_native L R i pL pR hL hR eL eR)
  intro x
  rw [network_raw]
  simp only [spliceTensor,FiniteNetwork.flipBit,hL,hR]

include pL pR hL hR in
theorem realizes_splice (family : SignatureFamily K)
    (vL : ∀v,(⟨L.shape.arity v,L.vertex v⟩ : AnySignature K)∈family)
    (vR : ∀v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature K)∈family)
    (eL : ∀e,L.edge e=.disequality) (eR : ∀e,R.edge e=.disequality) :
    Gadget.Realizes family .disequality (spliceTensor L.tensor R.tensor i) := by
  rw [← network_tensor L R i pL pR hL hR eL eR]
  exact realizes_network L R i pL pR hL hR family vL vR eL eR

end Holant.OpenNetworkComposition.Ordinary
