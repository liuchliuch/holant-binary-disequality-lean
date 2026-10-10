import Holant.OpenNetworkComposition.OrdinaryShape
import Holant.OpenNetworkComposition.Semantics

/-! Resource-preserving labelled constructor for a disjoint ordinary/ordinary
attachment. The corrected-tensor composition identity remains separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.Ordinary
variable {K VL VR FL FR EL ER : Type*} {n : ℕ}

abbrev network (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2) (i : Fin n)
    (pL : Σ v : VL,Fin (L.shape.arity v)) (pR : Σ v : VR,Fin (R.shape.arity v))
    (hL : L.shape.boundary i=.inl pL) (hR : R.shape.boundary 1=.inl pR) :
    FiniteNetwork K (VL ⊕ VR) (FL ⊕ FR) ((EL ⊕ ER) ⊕ Unit) n where
  shape := shape L.shape R.shape i pL pR hL hR
  vertex
    | .inl v => L.vertex v
    | .inr v => R.vertex v
  edge
    | .inl (.inl e) => L.edge e
    | .inl (.inr e) => R.edge e
    | .inr _ => .disequality

theorem network_edges_native (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2) (i : Fin n)
    (pL : Σ v : VL,Fin (L.shape.arity v)) (pR : Σ v : VR,Fin (R.shape.arity v))
    (hL : L.shape.boundary i=.inl pL) (hR : R.shape.boundary 1=.inl pR)
    (eL : ∀e,L.edge e=.disequality) (eR : ∀e,R.edge e=.disequality) :
    ∀e,(network L R i pL pR hL hR).edge e=.disequality := by
  rintro ((e|e)|u)
  · exact eL e
  · exact eR e
  · rfl

theorem realizes_network [CommSemiring K]
    [Fintype VL] [Fintype VR] [Fintype FL] [Fintype FR] [Fintype EL] [Fintype ER]
    (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2) (i : Fin n)
    (pL : Σ v : VL,Fin (L.shape.arity v)) (pR : Σ v : VR,Fin (R.shape.arity v))
    (hL : L.shape.boundary i=.inl pL) (hR : R.shape.boundary 1=.inl pR)
    (family : SignatureFamily K)
    (vL : ∀v,(⟨L.shape.arity v,L.vertex v⟩ : AnySignature K)∈family)
    (vR : ∀v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature K)∈family)
    (eL : ∀e,L.edge e=.disequality) (eR : ∀e,R.edge e=.disequality) :
    Gadget.Realizes family .disequality (network L R i pL pR hL hR).tensor := by
  apply FiniteNetwork.realizes
  · rintro (v|v)
    · exact vL v
    · exact vR v
  · exact network_edges_native L R i pL pR hL hR eL eR

end Holant.OpenNetworkComposition.Ordinary
