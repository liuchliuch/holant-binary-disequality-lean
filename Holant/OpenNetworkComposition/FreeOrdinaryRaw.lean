import Holant.OpenNetworkComposition.MixedWeights
import Holant.OpenNetworkComposition.FreeFreeRaw
import Holant.OpenNetworkComposition.BoundarySums

/-! Exact raw assignment law for a single left-free splice. No scalar
component is dropped when its selected free edge is replaced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.FreeOrdinary
variable {K VL FL EL VR FR ER : Type*} {n : ℕ}
variable [Fintype VL] [Fintype FL] [Fintype EL] [Fintype VR] [Fintype FR] [Fintype ER] [CommSemiring K]

def joinedAssignmentEquiv (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2) (f : FL) :
    (Ports (VL ⊕ VR) (FiniteShape.CutFree f ⊕ FR) (SumArity L.shape.arity R.shape.arity) → Bool) ≃
    ((L.shape.CutPorts f → Bool) × (Ports VR FR R.shape.arity → Bool)) :=
  (Equiv.arrowCongr (portSum L.shape.arity R.shape.arity) (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

variable (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2) (f : FL) (i : Fin n)
    (p : Σv,Fin (R.shape.arity v)) (hL : L.shape.boundary i=.inr f) (hR : R.shape.boundary 1=.inl p)

theorem joined_boundary_agrees_iff (zL : L.shape.CutPorts f → Bool) (zR : Ports VR FR R.shape.arity → Bool)
    (x : Fin n → Bool) :
    (∀j,joinedAssignment L R f zL zR ((network L R f i p hL hR).shape.boundary j)=x j) ↔
      L.shape.cutBoundaryAgrees f i hL zL x ∧ zR (R.shape.boundary 0)=x i := by
  have heval (j : Fin n) : joinedAssignment L R f zL zR ((network L R f i p hL hR).shape.boundary j)=
      Sum.elim zL zR (boundary L.shape R.shape f i hL j) := by
    simp only [joinedAssignment,network,shape,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply]
  simp only [heval]
  constructor
  · intro h
    constructor
    · intro j
      have hh := h j.val
      rw [boundary_away L.shape R.shape f i hL j.val j.property] at hh
      exact hh
    · have hh := h i
      rw [boundary_at] at hh
      exact hh
  · rintro ⟨hl,hr⟩ j
    by_cases hj : j=i
    · subst j; rw [boundary_at]; exact hr
    · rw [boundary_away L.shape R.shape f i hL j hj]
      exact hl ⟨j,hj⟩

theorem network_raw_eq_sum (x : Fin n → Bool) :
    (network L R f i p hL hR).raw x=
      ∑ zL : L.shape.CutPorts f → Bool,∑ zR : Ports VR FR R.shape.arity → Bool,
      if L.shape.cutBoundaryAgrees f i hL zL x ∧ zR (R.shape.boundary 0)=x i
      then (network L R f i p hL hR).weight (joinedAssignment L R f zL zR) else 0 := by
  classical
  let e := joinedAssignmentEquiv L R f
  let W := fun z : Ports (VL ⊕ VR) (FiniteShape.CutFree f ⊕ FR) (SumArity L.shape.arity R.shape.arity) → Bool =>
    if ∀j,z ((network L R f i p hL hR).shape.boundary j)=x j then (network L R f i p hL hR).weight z else 0
  have hs : (∑z,W z)=∑zz,W (e.symm zz) := (e.symm.sum_comp W).symm
  have hr : (network L R f i p hL hR).raw x=∑z,W z := by
    unfold FiniteNetwork.raw
    apply sum_instances
    intro z
    rfl
  rw [hr,hs,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro zL _
  apply Finset.sum_congr rfl
  intro zR _
  change W (joinedAssignment L R f zL zR)=_
  dsimp only [W]
  simp only [joined_boundary_agrees_iff]

theorem network_raw (eL : L.edge (L.shape.freeEdge f).1=.disequality) (x : Fin n → Bool) :
    (network L R f i p hL hR).raw x=∑a : Bool,L.raw (Function.update x i a)*R.raw (![x i,a]) := by
  rw [network_raw_eq_sum]
  simp_rw [L.raw_eq_cut_sum f i hL]
  unfold FiniteNetwork.raw
  simp only [FiniteShape.cutBoundaryAgrees_update,FiniteShape.boundary_binary_iff,
    Function.update_self,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [sum_three_swap]
  apply Finset.sum_congr rfl
  intro zL _
  apply Finset.sum_congr rfl
  intro zR _
  by_cases hl : L.shape.cutBoundaryAgrees f i hL zL x
  · by_cases hr : zR (R.shape.boundary 0)=x i
    · simp only [hl,hr,and_self,ite_true]
      rw [network_weight_identification L R f i p hL hR eL]
      cases ha : zR (R.shape.boundary 1) <;> simp [ha]
    · simp [hl,hr]
  · simp [hl]

end Holant.OpenNetworkComposition.FreeOrdinary
