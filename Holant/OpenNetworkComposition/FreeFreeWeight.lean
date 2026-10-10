import Holant.OpenNetworkComposition.FreeFreeTensor
import Holant.OpenNetworkComposition.FreeFreeNetwork

/-! Exact assignment-level weight factorization for disjoint free/free fusion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition
namespace FiniteNetwork
variable {K V F E : Type*} {n : ℕ}
variable [Fintype V] [Fintype F] [Fintype E] [CommSemiring K]

/-- The original vertex factors and exactly the retained edge factors. -/
def cutWeight (N : FiniteNetwork K V F E n) (f : F) (z : N.shape.CutPorts f → Bool) : K :=
  (∏ v,N.vertex v (fun k => z (.inl ⟨v,k⟩))) *
  ∏ e : N.shape.CutEdge f,(N.edge e.val).value (K := K)
    (z (N.shape.cutEnds f (e,false))) (z (N.shape.cutEnds f (e,true)))

theorem selected_edge_restored (N : FiniteNetwork K V F E n) (f : F)
    (he : N.edge (N.shape.freeEdge f).1=.disequality)
    (z : N.shape.CutPorts f → Bool) (a : Bool) :
    (N.edge (N.shape.freeEdge f).1).value (K := K)
      (N.shape.restoreAssignment f z a (N.shape.ends ((N.shape.freeEdge f).1,false)))
      (N.shape.restoreAssignment f z a (N.shape.ends ((N.shape.freeEdge f).1,true))) =
    Signature.disequality (K := K) a (z (N.shape.cutOpposite f)) := by
  rw [he]
  change Signature.disequality _ _ = _
  cases hb : (N.shape.freeEdge f).2
  · have hs : N.shape.ends ((N.shape.freeEdge f).1,false)=.inr f := by
      have hh : N.shape.ends ((N.shape.freeEdge f).1,(N.shape.freeEdge f).2)=.inr f :=
        N.shape.free_paired f
      simpa only [hb] using hh
    have ho : N.shape.ends ((N.shape.freeEdge f).1,true)=
        N.shape.cutEmbed f (N.shape.cutOpposite f) := by
      simp [hb]
    rw [hs,ho,FiniteShape.restoreAssignment_deleted,FiniteShape.restoreAssignment_retained]
  · have hs : N.shape.ends ((N.shape.freeEdge f).1,true)=.inr f := by
      have hh : N.shape.ends ((N.shape.freeEdge f).1,(N.shape.freeEdge f).2)=.inr f :=
        N.shape.free_paired f
      simpa only [hb] using hh
    have ho : N.shape.ends ((N.shape.freeEdge f).1,false)=
        N.shape.cutEmbed f (N.shape.cutOpposite f) := by
      simp [hb]
    rw [hs,ho,FiniteShape.restoreAssignment_deleted,FiniteShape.restoreAssignment_retained]
    cases a <;> cases hz : z (N.shape.cutOpposite f) <;> rfl

/-- Exact old-weight factorization, including every disconnected scalar factor. -/
theorem weight_restoreAssignment (N : FiniteNetwork K V F E n) (f : F)
    (he : N.edge (N.shape.freeEdge f).1=.disequality)
    (z : N.shape.CutPorts f → Bool) (a : Bool) :
    N.weight (N.shape.restoreAssignment f z a) =
      N.cutWeight f z * Signature.disequality a (z (N.shape.cutOpposite f)) := by
  classical
  unfold weight
  rw [Fintype.prod_eq_mul_prod_compl (N.shape.freeEdge f).1]
  rw [Finset.prod_subtype ({(N.shape.freeEdge f).1}ᶜ : Finset E)
    (p := fun e => e ≠ (N.shape.freeEdge f).1) (by simp)]
  rw [N.selected_edge_restored f he z a]
  have hv : (∏ v,N.vertex v (fun k => N.shape.restoreAssignment f z a (.inl ⟨v,k⟩))) =
      ∏ v,N.vertex v (fun k => z (.inl ⟨v,k⟩)) := by
    apply Finset.prod_congr rfl
    intro v _
    congr 1
  rw [hv]
  have hedge : (∏ e : N.shape.CutEdge f,(N.edge e.val).value (K := K)
      (N.shape.restoreAssignment f z a (N.shape.ends (e.val,false)))
      (N.shape.restoreAssignment f z a (N.shape.ends (e.val,true)))) =
      ∏ e : N.shape.CutEdge f,(N.edge e.val).value (K := K)
        (z (N.shape.cutEnds f (e,false))) (z (N.shape.cutEnds f (e,true))) := by
    apply Finset.prod_congr rfl
    intro e _
    have hk (b : Bool) : N.shape.restoreAssignment f z a (N.shape.ends (e.val,b)) =
        z (N.shape.cutEnds f (e,b)) := by
      calc
        _ = N.shape.restoreAssignment f z a (N.shape.cutEmbed f (N.shape.cutEnds f (e,b))) :=
          congrArg (N.shape.restoreAssignment f z a) (N.shape.cutEmbed_cutEnds f (e,b)).symm
        _ = _ := N.shape.restoreAssignment_retained f z a _
    exact congrArg₂ ((N.edge e.val).value (K := K)) (hk false) (hk true)
  rw [hedge]
  unfold cutWeight
  ac_rfl

end FiniteNetwork
namespace FreeFree
variable {K VL FL EL VR FR ER : Type*} {n : ℕ}
variable [Fintype VL] [Fintype FL] [Fintype EL]
    [Fintype VR] [Fintype FR] [Fintype ER] [CommSemiring K]

/-- The spliced assignment uses the original ordered coordinates on each side. -/
def joinedAssignment (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (fL : FL) (fR : FR) (zL : L.shape.CutPorts fL → Bool) (zR : R.shape.CutPorts fR → Bool) :
    Ports (VL ⊕ VR) (FiniteShape.CutFree fL ⊕ FiniteShape.CutFree fR)
      (SumArity L.shape.arity R.shape.arity) → Bool :=
  fun p => Sum.elim zL zR (portSum L.shape.arity R.shape.arity p)

/-- Exact weight of the constructed network, including all retained vertices and
all retained edges. -/
theorem network_weight (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.shape.boundary i=.inr fL) (hR : R.shape.boundary 1=.inr fR)
    (zL : L.shape.CutPorts fL → Bool) (zR : R.shape.CutPorts fR → Bool) :
    (network L R fL fR i hL hR).weight (joinedAssignment L R fL fR zL zR) =
      L.cutWeight fL zL * R.cutWeight fR zR *
        Signature.disequality (zL (L.shape.cutOpposite fL)) (zR (R.shape.cutOpposite fR)) := by
  unfold FiniteNetwork.weight
  simp only [Fintype.prod_sum_type,Fintype.prod_unique]
  simp only [network,shape,joinedAssignment,Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply,Equiv.apply_symm_apply]
  simp only [ends]
  change
    ((∏ v,L.vertex v (fun k => zL (.inl ⟨v,k⟩))) *
      (∏ v,R.vertex v (fun k => zR (.inl ⟨v,k⟩)))) *
    (((∏ e : L.shape.CutEdge fL,(L.edge e.val).value (K := K)
        (zL (L.shape.cutEnds fL (e,false))) (zL (L.shape.cutEnds fL (e,true)))) *
      (∏ e : R.shape.CutEdge fR,(R.edge e.val).value (K := K)
        (zR (R.shape.cutEnds fR (e,false))) (zR (R.shape.cutEnds fR (e,true))))) *
      Signature.disequality (K := K) (zL (L.shape.cutOpposite fL)) (zR (R.shape.cutOpposite fR))) = _
  unfold FiniteNetwork.cutWeight
  ac_rfl

/-- Summing the two removed free bits and their connecting native-X kernel is
exactly the weight of the explicit fused graph, with arbitrary surviving ports. -/
theorem network_weight_elimination (L : FiniteNetwork K VL FL EL n)
    (R : FiniteNetwork K VR FR ER 2) (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.shape.boundary i=.inr fL) (hR : R.shape.boundary 1=.inr fR)
    (eL : L.edge (L.shape.freeEdge fL).1=.disequality)
    (eR : R.edge (R.shape.freeEdge fR).1=.disequality)
    (zL : L.shape.CutPorts fL → Bool) (zR : R.shape.CutPorts fR → Bool) :
    (∑ a : Bool,∑ b : Bool,
      L.weight (L.shape.restoreAssignment fL zL a) *
      R.weight (R.shape.restoreAssignment fR zR b) * Signature.disequality a b) =
    (network L R fL fR i hL hR).weight (joinedAssignment L R fL fR zL zR) := by
  simp only [L.weight_restoreAssignment fL eL,R.weight_restoreAssignment fR eR]
  rw [native_three_edge_elimination,network_weight]

end FreeFree
end Holant.OpenNetworkComposition
