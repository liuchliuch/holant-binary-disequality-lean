import Holant.OpenNetworkComposition.OrdinaryFree
import Holant.OpenNetworkComposition.Semantics

/-! Original-label/default-edge preservation for the mixed disjoint splice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.OrdinaryFree
variable {K VL FL EL VR FR ER : Type*} {n : ℕ}

abbrev network (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (f : FR) (i : Fin n) (p : Σ v : VL,Fin (L.shape.arity v)) (hL : L.shape.boundary i=.inl p) (hR : R.shape.boundary 1=.inr f) :
    FiniteNetwork K (VL ⊕ VR) (FL ⊕ FiniteShape.CutFree f) (JoinEdges (EL := EL) R.shape f) n where
  shape := shape L.shape R.shape f i p hL hR
  vertex
    | .inl v => L.vertex v
    | .inr v => R.vertex v
  edge
    | .inl (.inl e) => L.edge e
    | .inl (.inr e) => R.edge e.val
    | .inr _ => .disequality

theorem network_edges_native (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (f : FR) (i : Fin n) (p : Σ v : VL,Fin (L.shape.arity v)) (hL : L.shape.boundary i=.inl p) (hR : R.shape.boundary 1=.inr f)
    (eL : ∀e,L.edge e=.disequality) (eR : ∀e,R.edge e=.disequality) :
    ∀e,(network L R f i p hL hR).edge e=.disequality := by
  rintro ((e|e)|u)
  · exact eL e
  · exact eR e.val
  · rfl

theorem realizes_network [CommSemiring K]
    [Fintype VL] [Fintype VR] [Fintype FL] [Fintype FR] [Fintype EL] [Fintype ER]
    (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (f : FR) (i : Fin n) (p : Σ v : VL,Fin (L.shape.arity v)) (hL : L.shape.boundary i=.inl p) (hR : R.shape.boundary 1=.inr f)
    (family : SignatureFamily K)
    (vL : ∀v,(⟨L.shape.arity v,L.vertex v⟩ : AnySignature K)∈family)
    (vR : ∀v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature K)∈family)
    (eL : ∀e,L.edge e=.disequality) (eR : ∀e,R.edge e=.disequality) :
    Gadget.Realizes family .disequality (network L R f i p hL hR).tensor := by
  classical
  apply FiniteNetwork.realizes
  · rintro (v|v)
    · exact vL v
    · exact vR v
  · exact network_edges_native L R f i p hL hR eL eR

end Holant.OpenNetworkComposition.OrdinaryFree
