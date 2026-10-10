import Holant.OpenNetworkComposition.FreeFreeWeight

/-! Assignment-sum semantics of the explicit disjoint free/free splice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition
namespace FiniteShape
variable {V F E : Type*} {n : ℕ}

def cutBoundaryAgrees (s : FiniteShape V F E n) (f : F) (i : Fin n)
    (hi : s.boundary i=.inr f) (z : s.CutPorts f → Bool) (x : Fin n → Bool) : Prop :=
  ∀ j : {j : Fin n // j≠i},z (s.cutBoundary f i hi j)=x j.val

theorem restore_boundary_agrees_iff (s : FiniteShape V F E n) (f : F) (i : Fin n)
    (hi : s.boundary i=.inr f) (z : s.CutPorts f → Bool) (x : Fin n → Bool) (a : Bool) :
    (∀ j,s.restoreAssignment f z a (s.boundary j)=x j) ↔
    a=x i ∧ s.cutBoundaryAgrees f i hi z x := by
  constructor
  · intro h
    constructor
    · simpa [hi] using h i
    · intro j
      have hh := h j.val
      rw [← s.cutEmbed_cutBoundary f i hi j,s.restoreAssignment_retained] at hh
      exact hh
  · rintro ⟨ha,h⟩ j
    by_cases hj : j=i
    · subst j; simpa [hi] using ha
    · rw [← s.cutEmbed_cutBoundary f i hi ⟨j,hj⟩,s.restoreAssignment_retained]
      exact h ⟨j,hj⟩

@[simp] theorem cutBoundaryAgrees_update (s : FiniteShape V F E n) (f : F) (i : Fin n)
    (hi : s.boundary i=.inr f) (z : s.CutPorts f → Bool) (x : Fin n → Bool) (a : Bool) :
    s.cutBoundaryAgrees f i hi z (Function.update x i a) ↔ s.cutBoundaryAgrees f i hi z x := by
  constructor
  · intro h j
    have hh := h j
    rwa [Function.update_of_ne j.property] at hh
  · intro h j
    rw [Function.update_of_ne j.property]
    exact h j

@[simp] theorem cutBoundaryAgrees_binary (s : FiniteShape V F E 2) (f : F)
    (hi : s.boundary 1=.inr f) (z : s.CutPorts f → Bool) (x : Fin 2 → Bool) :
    s.cutBoundaryAgrees f 1 hi z x ↔ z (s.cutBoundary f 1 hi ⟨0,by decide⟩)=x 0 := by
  constructor
  · intro h; exact h ⟨0,by decide⟩
  · intro h ⟨j,hj⟩
    have hj0 : j=0 := by fin_cases j <;> simp_all
    subst j
    exact h

end FiniteShape
namespace FiniteNetwork
variable {K V F E : Type*} {n : ℕ}
variable [Fintype V] [Fintype F] [Fintype E] [CommSemiring K]

/-- Exact raw tensor after isolating one free boundary assignment. -/
theorem raw_eq_cut_sum (N : FiniteNetwork K V F E n) (f : F) (i : Fin n)
    (hi : N.shape.boundary i=.inr f) (x : Fin n → Bool) :
    N.raw x = ∑ z : N.shape.CutPorts f → Bool,
      if N.shape.cutBoundaryAgrees f i hi z x
      then N.weight (N.shape.restoreAssignment f z (x i)) else 0 := by
  classical
  unfold raw
  calc
    _ = ∑ az : Bool × (N.shape.CutPorts f → Bool),
        if ∀ j,N.shape.restoreAssignment f az.2 az.1 (N.shape.boundary j)=x j
        then N.weight (N.shape.restoreAssignment f az.2 az.1) else 0 := by
      apply Fintype.sum_equiv (N.shape.cutAssignmentEquiv f)
      intro z
      have h := (N.shape.cutAssignmentEquiv f).symm_apply_apply z
      change N.shape.restoreAssignment f (fun p => z (N.shape.cutEmbed f p)) (z (.inr f)) = z at h
      simpa only [FiniteShape.cutAssignmentEquiv,Equiv.coe_fn_mk] using
        congrArg (fun w => if ∀ j,w (N.shape.boundary j)=x j then N.weight w else 0) h.symm
    _ = _ := by
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      simp only [N.shape.restore_boundary_agrees_iff f i hi]
      by_cases h : N.shape.cutBoundaryAgrees f i hi z x
      · simp [h]
      · simp [h]

end FiniteNetwork

namespace FreeFree
variable {K VL FL EL VR FR ER : Type*} {n : ℕ}
variable [Fintype VL] [Fintype FL] [Fintype EL]
    [Fintype VR] [Fintype FR] [Fintype ER] [CommSemiring K]

def joinedAssignmentEquiv (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (fL : FL) (fR : FR) :
    (Ports (VL ⊕ VR) (FiniteShape.CutFree fL ⊕ FiniteShape.CutFree fR)
      (SumArity L.shape.arity R.shape.arity) → Bool) ≃
    ((L.shape.CutPorts fL → Bool) × (R.shape.CutPorts fR → Bool)) :=
  (Equiv.arrowCongr (portSum L.shape.arity R.shape.arity) (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] theorem joinedAssignmentEquiv_symm (L : FiniteNetwork K VL FL EL n)
    (R : FiniteNetwork K VR FR ER 2) (fL : FL) (fR : FR)
    (zL : L.shape.CutPorts fL → Bool) (zR : R.shape.CutPorts fR → Bool) :
    (joinedAssignmentEquiv L R fL fR).symm (zL,zR)=joinedAssignment L R fL fR zL zR := rfl

theorem joined_boundary_agrees_iff (L : FiniteNetwork K VL FL EL n)
    (R : FiniteNetwork K VR FR ER 2) (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.shape.boundary i=.inr fL) (hR : R.shape.boundary 1=.inr fR)
    (zL : L.shape.CutPorts fL → Bool) (zR : R.shape.CutPorts fR → Bool) (x : Fin n → Bool) :
    (∀ j,joinedAssignment L R fL fR zL zR ((network L R fL fR i hL hR).shape.boundary j)=x j) ↔
    L.shape.cutBoundaryAgrees fL i hL zL x ∧
      zR (R.shape.cutBoundary fR 1 hR ⟨0,by decide⟩)=x i := by
  have heval (j : Fin n) :
      joinedAssignment L R fL fR zL zR ((network L R fL fR i hL hR).shape.boundary j) =
      Sum.elim zL zR (boundary L.shape R.shape fL fR i hL hR j) := by
    simp only [joinedAssignment,network,shape,Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply,Equiv.apply_symm_apply]
  simp only [heval]
  constructor
  · intro h
    constructor
    · intro j
      have hh := h j.val
      rw [boundary_away L.shape R.shape fL fR i hL hR _ j.property] at hh
      exact hh
    · have hh := h i
      rw [boundary_at] at hh
      exact hh
  · rintro ⟨hl,hr⟩ j
    by_cases hj : j=i
    · subst j
      rw [boundary_at]
      exact hr
    · rw [boundary_away L.shape R.shape fL fR i hL hR j hj]
      exact hl ⟨j,hj⟩

private theorem sum_instances {A : Type*} (I J : Fintype A) (f g : A → K)
    (h : ∀a,f a=g a) :
    (@Finset.univ A I).sum f=(@Finset.univ A J).sum g := by
  have he : I=J := Subsingleton.elim _ _
  cases he
  exact Finset.sum_congr rfl (fun a _ => h a)

/-- Raw semantics of the fused graph as a sum over the two disjoint retained
assignment spaces, before eliminating the two deleted free bits. -/
theorem network_raw_eq_sum (L : FiniteNetwork K VL FL EL n)
    (R : FiniteNetwork K VR FR ER 2) (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.shape.boundary i=.inr fL) (hR : R.shape.boundary 1=.inr fR) (x : Fin n → Bool) :
    (network L R fL fR i hL hR).raw x =
      ∑ zL : L.shape.CutPorts fL → Bool,∑ zR : R.shape.CutPorts fR → Bool,
      if L.shape.cutBoundaryAgrees fL i hL zL x ∧
        zR (R.shape.cutBoundary fR 1 hR ⟨0,by decide⟩)=x i
      then (network L R fL fR i hL hR).weight (joinedAssignment L R fL fR zL zR) else 0 := by
  classical
  let e := joinedAssignmentEquiv L R fL fR
  let W := fun z : Ports (VL ⊕ VR) (FiniteShape.CutFree fL ⊕ FiniteShape.CutFree fR)
      (SumArity L.shape.arity R.shape.arity) → Bool =>
    if ∀ j,z ((network L R fL fR i hL hR).shape.boundary j)=x j
    then (network L R fL fR i hL hR).weight z else 0
  have hs : (∑ z,W z) = ∑ zz,W (e.symm zz) := (e.symm.sum_comp W).symm
  have hraw : (network L R fL fR i hL hR).raw x = ∑ z,W z := by
    unfold FiniteNetwork.raw
    apply sum_instances
    intro z
    rfl
  rw [hraw,hs,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro zL _
  apply Finset.sum_congr rfl
  intro zR _
  change W (joinedAssignment L R fL fR zL zR) = _
  dsimp only [W]
  simp only [joined_boundary_agrees_iff]

private theorem sum_four_swap {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (g : A → B → C → D → K) :
    (∑ a,∑ b,∑ c,∑ d,g a b c d) = ∑ c,∑ d,∑ a,∑ b,g a b c d := by
  calc
    _ = ∑ a,∑ c,∑ b,∑ d,g a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c,∑ a,∑ b,∑ d,g a b c d := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      calc
        _ = ∑ a,∑ d,∑ b,g a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]

/-- Exact raw contraction law for the constructed free/free splice. Only the
two removed edges must be native-X; every other original factor is retained. -/
theorem network_raw (L : FiniteNetwork K VL FL EL n)
    (R : FiniteNetwork K VR FR ER 2) (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.shape.boundary i=.inr fL) (hR : R.shape.boundary 1=.inr fR)
    (eL : L.edge (L.shape.freeEdge fL).1=.disequality)
    (eR : R.edge (R.shape.freeEdge fR).1=.disequality) (x : Fin n → Bool) :
    (network L R fL fR i hL hR).raw x =
      ∑ a : Bool,∑ b : Bool,L.raw (Function.update x i a) * R.raw (![x i,b]) *
        Signature.disequality a b := by
  classical
  rw [network_raw_eq_sum]
  simp_rw [L.raw_eq_cut_sum fL i hL,R.raw_eq_cut_sum fR 1 hR]
  simp only [FiniteShape.cutBoundaryAgrees_update,FiniteShape.cutBoundaryAgrees_binary,
    Function.update_self,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [sum_four_swap]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro zL _
  apply Finset.sum_congr rfl
  intro zR _
  by_cases hl : L.shape.cutBoundaryAgrees fL i hL zL x
  · by_cases hr : zR (R.shape.cutBoundary fR 1 hR ⟨0,by decide⟩)=x i
    · simp only [hl,hr,and_self,ite_true]
      exact (network_weight_elimination L R fL fR i hL hR eL eR zL zR).symm
    · simp [hl,hr]
  · simp [hl]

end FreeFree
end Holant.OpenNetworkComposition
