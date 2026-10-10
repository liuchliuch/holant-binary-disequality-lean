import Holant.OpenNetworkComposition.OrdinaryFreeNetwork
import Holant.OpenNetworkComposition.FreeOrdinaryNetwork
import Holant.OpenNetworkComposition.FreeFreeWeight

/-! Exact assignment-level weights of both mixed disjoint splices. The selected
free coordinate is restored at the ordinary coordinate's bit; native-X boundary
correction will turn this raw identification into the required tensor X-gluing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition
namespace OrdinaryFree
variable {K VL FL EL VR FR ER : Type*} {n : ℕ}
variable [Fintype VL] [Fintype FL] [Fintype EL] [Fintype VR] [Fintype FR] [Fintype ER] [CommSemiring K]

def joinedAssignment (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2) (f : FR)
    (zL : Ports VL FL L.shape.arity → Bool) (zR : R.shape.CutPorts f → Bool) :
    Ports (VL ⊕ VR) (FL ⊕ FiniteShape.CutFree f) (SumArity L.shape.arity R.shape.arity) → Bool :=
  fun p => Sum.elim zL zR (portSum L.shape.arity R.shape.arity p)

theorem network_weight (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (f : FR) (i : Fin n) (p : Σv,Fin (L.shape.arity v))
    (hL : L.shape.boundary i=.inl p) (hR : R.shape.boundary 1=.inr f)
    (zL : Ports VL FL L.shape.arity → Bool) (zR : R.shape.CutPorts f → Bool) :
    (network L R f i p hL hR).weight (joinedAssignment L R f zL zR)=
      L.weight zL*R.cutWeight f zR*Signature.disequality (zL (L.shape.boundary i)) (zR (R.shape.cutOpposite f)) := by
  unfold FiniteNetwork.weight
  simp only [Fintype.prod_sum_type,Fintype.prod_unique]
  simp only [network,shape,joinedAssignment,Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply,Equiv.apply_symm_apply,ends]
  change ((∏v,L.vertex v (fun k => zL (.inl ⟨v,k⟩)))*(∏v,R.vertex v (fun k => zR (.inl ⟨v,k⟩))))*
      (((∏e,(L.edge e).value (zL (L.shape.ends (e,false))) (zL (L.shape.ends (e,true))))*
        (∏e : R.shape.CutEdge f,(R.edge e.val).value
          (zR (R.shape.cutEnds f (e,false))) (zR (R.shape.cutEnds f (e,true)))))*
       Signature.disequality (zL (L.shape.boundary i)) (zR (R.shape.cutOpposite f)))=_
  unfold FiniteNetwork.cutWeight
  ac_rfl

theorem network_weight_identification (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (f : FR) (i : Fin n) (p : Σv,Fin (L.shape.arity v))
    (hL : L.shape.boundary i=.inl p) (hR : R.shape.boundary 1=.inr f)
    (eR : R.edge (R.shape.freeEdge f).1=.disequality)
    (zL : Ports VL FL L.shape.arity → Bool) (zR : R.shape.CutPorts f → Bool) :
    (network L R f i p hL hR).weight (joinedAssignment L R f zL zR)=
      L.weight zL*R.weight (R.shape.restoreAssignment f zR (zL (L.shape.boundary i))) := by
  rw [network_weight,R.weight_restoreAssignment f eR]
  ac_rfl

end OrdinaryFree
namespace FreeOrdinary
variable {K VL FL EL VR FR ER : Type*} {n : ℕ}
variable [Fintype VL] [Fintype FL] [Fintype EL] [Fintype VR] [Fintype FR] [Fintype ER] [CommSemiring K]

def joinedAssignment (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2) (f : FL)
    (zL : L.shape.CutPorts f → Bool) (zR : Ports VR FR R.shape.arity → Bool) :
    Ports (VL ⊕ VR) (FiniteShape.CutFree f ⊕ FR) (SumArity L.shape.arity R.shape.arity) → Bool :=
  fun p => Sum.elim zL zR (portSum L.shape.arity R.shape.arity p)

theorem network_weight (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (f : FL) (i : Fin n) (p : Σv,Fin (R.shape.arity v))
    (hL : L.shape.boundary i=.inr f) (hR : R.shape.boundary 1=.inl p)
    (zL : L.shape.CutPorts f → Bool) (zR : Ports VR FR R.shape.arity → Bool) :
    (network L R f i p hL hR).weight (joinedAssignment L R f zL zR)=
      L.cutWeight f zL*R.weight zR*Signature.disequality (zL (L.shape.cutOpposite f)) (zR (R.shape.boundary 1)) := by
  unfold FiniteNetwork.weight
  simp only [Fintype.prod_sum_type,Fintype.prod_unique]
  simp only [network,shape,joinedAssignment,Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply,Equiv.apply_symm_apply,ends]
  change ((∏v,L.vertex v (fun k => zL (.inl ⟨v,k⟩)))*(∏v,R.vertex v (fun k => zR (.inl ⟨v,k⟩))))*
      (((∏e : L.shape.CutEdge f,(L.edge e.val).value
          (zL (L.shape.cutEnds f (e,false))) (zL (L.shape.cutEnds f (e,true))))*
        (∏e,(R.edge e).value (zR (R.shape.ends (e,false))) (zR (R.shape.ends (e,true)))))*
       Signature.disequality (zL (L.shape.cutOpposite f)) (zR (R.shape.boundary 1)))=_
  unfold FiniteNetwork.cutWeight
  ac_rfl

theorem network_weight_identification (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (f : FL) (i : Fin n) (p : Σv,Fin (R.shape.arity v))
    (hL : L.shape.boundary i=.inr f) (hR : R.shape.boundary 1=.inl p)
    (eL : L.edge (L.shape.freeEdge f).1=.disequality)
    (zL : L.shape.CutPorts f → Bool) (zR : Ports VR FR R.shape.arity → Bool) :
    (network L R f i p hL hR).weight (joinedAssignment L R f zL zR)=
      L.weight (L.shape.restoreAssignment f zL (zR (R.shape.boundary 1)))*R.weight zR := by
  rw [network_weight,L.weight_restoreAssignment f eL]
  have hs : Signature.disequality (K := K) (zL (L.shape.cutOpposite f)) (zR (R.shape.boundary 1))=
      Signature.disequality (K := K) (zR (R.shape.boundary 1)) (zL (L.shape.cutOpposite f)) := by
    cases zL (L.shape.cutOpposite f) <;> cases zR (R.shape.boundary 1) <;> rfl
  rw [hs]
  ac_rfl

end FreeOrdinary
end Holant.OpenNetworkComposition
