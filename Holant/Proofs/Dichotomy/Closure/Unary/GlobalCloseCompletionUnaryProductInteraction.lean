import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductTrees

/-! A nonzero anchored binary minor identifies a common factor block in an
actual tensor decomposition. This is the scope-detection step for binary
factors in zero-cap UPF propagation; the factor partition is not assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductInteraction
open Holant
open scoped BigOperators
namespace P
export GlobalCloseCompletionUnaryPinnedProduct (single cap)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

def double (i j : Fin n) : Fin n→Bool := Function.update (P.single i) j true
def minor (f : Signature K n) (i j : Fin n) : K :=
  f (fun _=>false)*f (double i j)-f (P.single i)*f (P.single j)
def owner (D : TensorDecomposition K n) (i : Fin n) : Fin D.count := (D.ports.symm i).1

theorem port_ne (D : TensorDecomposition K n) (v : Fin D.count) (i : Fin n)
    (different : owner D i≠v) (k : Fin (D.arity v)) : D.ports ⟨v,k⟩≠i := by
  intro same
  have h:=congrArg (owner D) same
  simp only [owner,Equiv.symm_apply_apply] at h
  exact different h.symm

theorem single_restrict (D : TensorDecomposition K n) (v : Fin D.count) (i : Fin n)
    (different : owner D i≠v) :
    (fun k=>P.single i (D.ports ⟨v,k⟩))=(fun _=>false) := by
  funext k
  simp [P.single,Function.update_of_ne (port_ne D v i different k)]

theorem double_restrict_left (D : TensorDecomposition K n) (v : Fin D.count) (i j : Fin n)
    (different : owner D i≠v) :
    (fun k=>double i j (D.ports ⟨v,k⟩))=(fun k=>P.single j (D.ports ⟨v,k⟩)) := by
  funext k
  by_cases same : D.ports ⟨v,k⟩=j
  · simp [double,P.single,same]
  · simp [double,P.single,Function.update_of_ne same,
      Function.update_of_ne (port_ne D v i different k)]

theorem double_comm (i j : Fin n) : double i j=double j i := by
  funext k
  by_cases hi : k=i
  · subst k
    by_cases hj : i=j
    · subst j
      simp [double,P.single]
    · simp [double,P.single,hj,Ne.symm hj]
  · by_cases hj : k=j
    · subst k
      simp [double,P.single,hi,Ne.symm hi]
    · simp [double,P.single,hi,hj]

theorem different_blocks_minor (D : TensorDecomposition K n) (i j : Fin n)
    (different : owner D i≠owner D j) : minor D.value i j=0 := by
  have localIdentity (v : Fin D.count) :
      D.factor v (fun _=>false)*D.factor v (fun k=>double i j (D.ports ⟨v,k⟩))=
        D.factor v (fun k=>P.single i (D.ports ⟨v,k⟩))*
          D.factor v (fun k=>P.single j (D.ports ⟨v,k⟩)) := by
    by_cases left : owner D i=v
    · have right : owner D j≠v := fun h=>different (left.trans h.symm)
      rw [single_restrict D v j right,double_comm i j,double_restrict_left D v j i right]
      exact mul_comm _ _
    · rw [single_restrict D v i left,double_restrict_left D v i j left]
  have products :
      (∏v,D.factor v (fun _=>false))*(∏v,D.factor v (fun k=>double i j (D.ports ⟨v,k⟩)))=
        (∏v,D.factor v (fun k=>P.single i (D.ports ⟨v,k⟩)))*
          (∏v,D.factor v (fun k=>P.single j (D.ports ⟨v,k⟩))) := by
    rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun v _=>localIdentity v)
  unfold minor TensorDecomposition.value
  calc
    _=(D.scale : K)^2*((∏v,D.factor v (fun _=>false))*
        (∏v,D.factor v (fun k=>double i j (D.ports ⟨v,k⟩)))-
        (∏v,D.factor v (fun k=>P.single i (D.ports ⟨v,k⟩)))*
          (∏v,D.factor v (fun k=>P.single j (D.ports ⟨v,k⟩)))) := by ring
    _=0 := by rw [products];ring

theorem same_block_of_minor (D : TensorDecomposition K n) (i j : Fin n)
    (nonzero : minor D.value i j≠0) : owner D i=owner D j := by
  by_contra different
  exact nonzero (different_blocks_minor D i j different)

/-- Pinning a third port to zero preserves the actual anchored minor. -/
theorem cap_minor (f : Signature K n) (i j k : Fin n) (ik : i≠k) (jk : j≠k) :
    minor (P.cap k f) i j=minor f i j := by
  have noChange : Function.update (double i j) k false=double i j := by
    funext l
    by_cases hl : l=k
    · subst l
      simp [double,P.single,Ne.symm ik,Ne.symm jk]
    · simp [hl]
  simp only [minor,GlobalCloseCompletionUnaryPinnedProduct.cap_origin,
    GlobalCloseCompletionUnaryPinnedProduct.cap_single f k i ik,
    GlobalCloseCompletionUnaryPinnedProduct.cap_single f k j jk]
  rw [P.cap,noChange]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductInteraction
end
