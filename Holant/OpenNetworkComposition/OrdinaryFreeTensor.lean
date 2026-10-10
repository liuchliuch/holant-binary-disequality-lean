import Holant.OpenNetworkComposition.OrdinaryFreeRaw
import Holant.OpenNetworkComposition.BoundaryKinds

/-! Corrected native-X tensor law for the mixed disjoint splice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.OrdinaryFree
variable {K VL FL EL VR FR ER : Type*} {n : ℕ}
variable (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (f : FR) (i : Fin n) (p : Σv,Fin (L.shape.arity v)) (hL : L.shape.boundary i=.inl p) (hR : R.shape.boundary 1=.inr f)

theorem boundaryFlip_network_away (x : Fin n → Bool) (j : Fin n) (hj : j≠i) :
    (network L R f i p hL hR).boundaryFlip x j=L.boundaryFlip x j := by
  rw [boundaryFlip_portFlip,boundaryFlip_portFlip]
  change portFlip ((portSum L.shape.arity R.shape.arity).symm
    (boundary L.shape R.shape f i hR j)) (x j)=portFlip (L.shape.boundary j) (x j)
  rw [boundary_away L.shape R.shape f i hR j hj,portFlip_sum_left]

theorem boundaryFlip_network_at (x : Fin n → Bool) :
    (network L R f i p hL hR).boundaryFlip x i=R.flipBit 0 (x i) := by
  rw [boundaryFlip_portFlip,flipBit_portFlip]
  change portFlip ((portSum L.shape.arity R.shape.arity).symm
    (boundary L.shape R.shape f i hR i)) (x i)=portFlip (R.shape.boundary 0) (x i)
  rw [boundary_at,portFlip_sum_right,portFlip_cut,R.shape.cutEmbed_cutBoundary]

variable [Fintype VL] [Fintype FL] [Fintype EL] [Fintype VR] [Fintype FR] [Fintype ER] [CommSemiring K]

theorem network_tensor (eL : ∀e,L.edge e=.disequality) (eR : ∀e,R.edge e=.disequality) :
    (network L R f i p hL hR).tensor=spliceTensor L.tensor R.tensor i := by
  apply tensor_splice_of_raw L R (network L R f i p hL hR) i
    (boundaryFlip_network_away L R f i p hL hR) (boundaryFlip_network_at L R f i p hL hR)
    eL eR (network_edges_native L R f i p hL hR eL eR)
  intro x
  rw [network_raw L R f i p hL hR (eR _)]
  simp [FiniteNetwork.flipBit,hL,hR,Fintype.sum_bool,Signature.disequality]

include f p hL hR in
theorem realizes_splice (family : SignatureFamily K)
    (vL : ∀v,(⟨L.shape.arity v,L.vertex v⟩ : AnySignature K)∈family)
    (vR : ∀v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature K)∈family)
    (eL : ∀e,L.edge e=.disequality) (eR : ∀e,R.edge e=.disequality) :
    Gadget.Realizes family .disequality (spliceTensor L.tensor R.tensor i) := by
  rw [← network_tensor L R f i p hL hR eL eR]
  exact realizes_network L R f i p hL hR family vL vR eL eR

end Holant.OpenNetworkComposition.OrdinaryFree
