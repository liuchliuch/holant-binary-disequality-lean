import Holant.OpenNetworkComposition.OrdinaryNetwork
import Holant.OpenNetworkComposition.BoundarySums
import Holant.OpenNetworkComposition.FreeFreeTensor

/-! Exact raw assignment-sum semantics of the ordinary/ordinary disjoint splice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.Ordinary
variable {K VL FL EL VR FR ER : Type*} {n : ℕ}
variable [Fintype VL] [Fintype FL] [Fintype EL] [Fintype VR] [Fintype FR] [Fintype ER] [CommSemiring K]

def joinedAssignment (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (zL : Ports VL FL L.shape.arity → Bool) (zR : Ports VR FR R.shape.arity → Bool) :
    Ports (VL ⊕ VR) (FL ⊕ FR) (SumArity L.shape.arity R.shape.arity) → Bool :=
  fun p => Sum.elim zL zR (portSum L.shape.arity R.shape.arity p)

def joinedAssignmentEquiv (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2) :
    (Ports (VL ⊕ VR) (FL ⊕ FR) (SumArity L.shape.arity R.shape.arity) → Bool) ≃
    ((Ports VL FL L.shape.arity → Bool) × (Ports VR FR R.shape.arity → Bool)) :=
  (Equiv.arrowCongr (portSum L.shape.arity R.shape.arity) (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] theorem joined_left (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (zL : Ports VL FL L.shape.arity → Bool) (zR : Ports VR FR R.shape.arity → Bool)
    (p : Ports VL FL L.shape.arity) : joinedAssignment L R zL zR (leftPort L.shape.arity R.shape.arity p)=zL p := by
  simp [joinedAssignment]
@[simp] theorem joined_right (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (zL : Ports VL FL L.shape.arity → Bool) (zR : Ports VR FR R.shape.arity → Bool)
    (p : Ports VR FR R.shape.arity) : joinedAssignment L R zL zR (rightPort L.shape.arity R.shape.arity p)=zR p := by
  simp [joinedAssignment]

variable (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2) (i : Fin n)
    (pL : Σv,Fin (L.shape.arity v)) (pR : Σv,Fin (R.shape.arity v))
    (hL : L.shape.boundary i=.inl pL) (hR : R.shape.boundary 1=.inl pR)

theorem network_weight (zL : Ports VL FL L.shape.arity → Bool) (zR : Ports VR FR R.shape.arity → Bool) :
    (network L R i pL pR hL hR).weight (joinedAssignment L R zL zR)=
      L.weight zL*R.weight zR*Signature.disequality (zL (L.shape.boundary i)) (zR (R.shape.boundary 1)) := by
  have he (e : ((EL ⊕ ER) ⊕ Unit) × Bool) :
      (network L R i pL pR hL hR).shape.ends e=endpoint L.shape R.shape i e := rfl
  unfold FiniteNetwork.weight
  simp only [he,Fintype.prod_sum_type,Fintype.prod_unique]
  simp only [network,endpoint,joined_left,joined_right]
  have hvl (v : VL) (k : Fin (L.shape.arity v)) :
      joinedAssignment L R zL zR (.inl ⟨.inl v,k⟩)=zL (.inl ⟨v,k⟩) := rfl
  have hvr (v : VR) (k : Fin (R.shape.arity v)) :
      joinedAssignment L R zL zR (.inl ⟨.inr v,k⟩)=zR (.inl ⟨v,k⟩) := rfl
  simp only [hvl,hvr,EdgeKind.value]
  ac_rfl

theorem joined_boundary_agrees_iff (zL : Ports VL FL L.shape.arity → Bool) (zR : Ports VR FR R.shape.arity → Bool)
    (x : Fin n → Bool) :
    (∀j,joinedAssignment L R zL zR ((network L R i pL pR hL hR).shape.boundary j)=x j) ↔
      L.shape.awayAgrees i zL x ∧ zR (R.shape.boundary 0)=x i := by
  have heval (j : Fin n) : joinedAssignment L R zL zR ((network L R i pL pR hL hR).shape.boundary j)=
      if j=i then zR (R.shape.boundary 0) else zL (L.shape.boundary j) := by
    by_cases hj : j=i <;> simp [joinedAssignment,network,shape,boundary,hj]
  simp only [heval]
  constructor
  · intro h
    exact ⟨fun j hj => by simpa [hj] using h j,by simpa using h i⟩
  · rintro ⟨hl,hr⟩ j
    by_cases hj : j=i
    · subst j; simpa using hr
    · simpa [hj] using hl j hj

theorem network_raw_eq_sum (x : Fin n → Bool) :
    (network L R i pL pR hL hR).raw x=
      ∑ zL : Ports VL FL L.shape.arity → Bool,∑ zR : Ports VR FR R.shape.arity → Bool,
      if L.shape.awayAgrees i zL x ∧ zR (R.shape.boundary 0)=x i then
        L.weight zL*R.weight zR*Signature.disequality (zL (L.shape.boundary i)) (zR (R.shape.boundary 1)) else 0 := by
  classical
  let e := joinedAssignmentEquiv L R
  let W := fun z : Ports (VL ⊕ VR) (FL ⊕ FR) (SumArity L.shape.arity R.shape.arity) → Bool =>
    if ∀j,z ((network L R i pL pR hL hR).shape.boundary j)=x j then
      (network L R i pL pR hL hR).weight z else 0
  have hs : (∑z,W z)=∑zz,W (e.symm zz) := (e.symm.sum_comp W).symm
  have hr : (network L R i pL pR hL hR).raw x=∑z,W z := by
    unfold FiniteNetwork.raw
    apply sum_instances
    intro z
    rfl
  rw [hr,hs,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro zL _
  apply Finset.sum_congr rfl
  intro zR _
  change W (joinedAssignment L R zL zR)=_
  dsimp only [W]
  simp only [joined_boundary_agrees_iff,network_weight]

/-- The new edge joins the two independent selected original port assignments. -/
theorem network_raw (x : Fin n → Bool) :
    (network L R i pL pR hL hR).raw x=spliceTensor L.raw R.raw i x := by
  rw [network_raw_eq_sum]
  unfold spliceTensor FiniteNetwork.raw
  simp only [FiniteShape.boundary_update_iff,FiniteShape.boundary_binary_iff]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro zL _
  apply Finset.sum_congr rfl
  intro zR _
  by_cases hl : L.shape.awayAgrees i zL x
  · by_cases hr : zR (R.shape.boundary 0)=x i
    · cases ha : zL (L.shape.boundary i) <;> cases hb : zR (R.shape.boundary 1) <;> simp [hl,hr,ha,hb]
    · simp [hl,hr]
  · simp [hl]

end Holant.OpenNetworkComposition.Ordinary
