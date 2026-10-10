import Holant.OpenNetworkComposition.FreeFreeSplice
import Holant.OpenNetworkComposition.Semantics

/-! Labelled disjoint free/free splice. Retained vertices keep their original
ordered signatures, retained edges keep their original kind, and the sole new
edge is native disequality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.FreeFree
variable {K VL FL EL VR FR ER : Type*} {n : ℕ}

/-- Explicit, finite, disjoint free/free fusion, ready for `toOpen`. -/
abbrev network (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.shape.boundary i=.inr fL) (hR : R.shape.boundary 1=.inr fR) :
    FiniteNetwork K (VL ⊕ VR) (FiniteShape.CutFree fL ⊕ FiniteShape.CutFree fR)
      (SpliceEdges L.shape R.shape fL fR) n where
  shape := shape L.shape R.shape fL fR i hL hR
  vertex
    | .inl v => L.vertex v
    | .inr v => R.vertex v
  edge
    | .inl (.inl e) => L.edge e.val
    | .inl (.inr e) => R.edge e.val
    | .inr _ => .disequality

@[simp] theorem network_vertex_left (L : FiniteNetwork K VL FL EL n)
    (R : FiniteNetwork K VR FR ER 2) (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.shape.boundary i=.inr fL) (hR : R.shape.boundary 1=.inr fR) (v : VL) :
    (network L R fL fR i hL hR).vertex (.inl v)=L.vertex v := rfl

@[simp] theorem network_vertex_right (L : FiniteNetwork K VL FL EL n)
    (R : FiniteNetwork K VR FR ER 2) (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.shape.boundary i=.inr fL) (hR : R.shape.boundary 1=.inr fR) (v : VR) :
    (network L R fL fR i hL hR).vertex (.inr v)=R.vertex v := rfl

theorem network_edges_native (L : FiniteNetwork K VL FL EL n)
    (R : FiniteNetwork K VR FR ER 2) (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.shape.boundary i=.inr fL) (hR : R.shape.boundary 1=.inr fR)
    (eL : ∀ e,L.edge e=.disequality) (eR : ∀ e,R.edge e=.disequality) :
    ∀ e,(network L R fL fR i hL hR).edge e=.disequality := by
  rintro ((e|e)|u)
  · exact eL e.val
  · exact eR e.val
  · rfl

/-- Actual gadget provenance for the explicit constructed tensor. The exact
contraction identity is a separate semantic obligation, not assumed here. -/
theorem realizes_network [CommSemiring K]
    [Fintype VL] [Fintype FL] [Fintype EL]
    [Fintype VR] [Fintype FR] [Fintype ER]
    (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.shape.boundary i=.inr fL) (hR : R.shape.boundary 1=.inr fR)
    (family : SignatureFamily K)
    (vL : ∀ v,(⟨L.shape.arity v,L.vertex v⟩ : AnySignature K) ∈ family)
    (vR : ∀ v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature K) ∈ family)
    (eL : ∀ e,L.edge e=.disequality) (eR : ∀ e,R.edge e=.disequality) :
    Gadget.Realizes family .disequality (network L R fL fR i hL hR).tensor := by
  classical
  apply FiniteNetwork.realizes
  · rintro (v|v)
    · exact vL v
    · exact vR v
  · exact network_edges_native L R fL fR i hL hR eL eR

end Holant.OpenNetworkComposition.FreeFree
