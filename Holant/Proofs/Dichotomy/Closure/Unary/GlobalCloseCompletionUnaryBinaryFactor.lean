import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryInteractionMatching

/-! A selected nonzero anchored binary minor determines its exact factor in
every small tensor decomposition, and hence in every disjoint zero cap.
The factor is the original pair section normalized by the original zero
entry, so cross-cap propagation retains one concrete coefficient table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryFactor
open Holant
open scoped BigOperators
namespace I
export GlobalCloseCompletionUnaryProductInteraction (owner minor port_ne cap_minor same_block_of_minor)
export GlobalCloseCompletionUnaryInteractionMatching (no_three)
end I
namespace P
export GlobalCloseCompletionUnaryPinnedProduct (cap cap_origin)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

def pair (i j : Fin n) (a b : Bool) : Fin n→Bool :=
  Function.update (Function.update (fun _=>false) i a) j b
def outside (i j : Fin n) (x : Fin n→Bool) : Fin n→Bool :=
  Function.update (Function.update x i false) j false

theorem covers_block (D : TensorDecomposition K n) (v : Fin D.count) (small : D.arity v≤2)
    (i j : Fin n) (different : i≠j) (hi : I.owner D i=v) (hj : I.owner D j=v)
    (k : Fin (D.arity v)) : D.ports ⟨v,k⟩=i ∨ D.ports ⟨v,k⟩=j := by
  by_contra none
  push Not at none
  exact I.no_three D v small i j (D.ports ⟨v,k⟩) different none.1.symm none.2.symm hi hj
    (by simp [I.owner])

theorem factor_identity (D : TensorDecomposition K n) (small : ∀v,D.arity v≤2)
    (i j : Fin n) (different : i≠j) (same : I.owner D i=I.owner D j) (x : Fin n→Bool) :
    D.value x*D.value (fun _=>false)=D.value (pair i j (x i) (x j))*D.value (outside i j x) := by
  classical
  have localIdentity (v : Fin D.count) :
      D.factor v (fun k=>x (D.ports ⟨v,k⟩))*D.factor v (fun _=>false)=
        D.factor v (fun k=>pair i j (x i) (x j) (D.ports ⟨v,k⟩))*
          D.factor v (fun k=>outside i j x (D.ports ⟨v,k⟩)) := by
    by_cases hv : I.owner D i=v
    · have hj : I.owner D j=v := same.symm.trans hv
      have pairExact : (fun k=>pair i j (x i) (x j) (D.ports ⟨v,k⟩))=
          (fun k=>x (D.ports ⟨v,k⟩)) := by
        funext k
        rcases covers_block D v (small v) i j different hv hj k with h|h
        · simp [pair,h,different]
        · simp [pair,h]
      have outsideExact : (fun k=>outside i j x (D.ports ⟨v,k⟩))=(fun _=>false) := by
        funext k
        rcases covers_block D v (small v) i j different hv hj k with h|h
        · simp [outside,h,different]
        · simp [outside,h]
      rw [pairExact,outsideExact]
    · have hj : I.owner D j≠v := fun h=>hv (same.trans h)
      have pairExact : (fun k=>pair i j (x i) (x j) (D.ports ⟨v,k⟩))=(fun _=>false) := by
        funext k
        simp [pair,Function.update_of_ne (I.port_ne D v i hv k),Function.update_of_ne (I.port_ne D v j hj k)]
      have outsideExact : (fun k=>outside i j x (D.ports ⟨v,k⟩))=
          (fun k=>x (D.ports ⟨v,k⟩)) := by
        funext k
        simp [outside,Function.update_of_ne (I.port_ne D v i hv k),Function.update_of_ne (I.port_ne D v j hj k)]
      rw [pairExact,outsideExact]
      exact mul_comm _ _
  have products :
      (∏v,D.factor v (fun k=>x (D.ports ⟨v,k⟩)))*(∏v,D.factor v (fun _=>false))=
        (∏v,D.factor v (fun k=>pair i j (x i) (x j) (D.ports ⟨v,k⟩)))*
          (∏v,D.factor v (fun k=>outside i j x (D.ports ⟨v,k⟩))) := by
    rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun v _=>localIdentity v)
  unfold TensorDecomposition.value
  calc
    _=(D.scale : K)^2*((∏v,D.factor v (fun k=>x (D.ports ⟨v,k⟩)))*(∏v,D.factor v (fun _=>false))) := by ring
    _=(D.scale : K)^2*((∏v,D.factor v (fun k=>pair i j (x i) (x j) (D.ports ⟨v,k⟩)))*
        (∏v,D.factor v (fun k=>outside i j x (D.ports ⟨v,k⟩)))) := by rw [products]
    _=_:=by ring

theorem small_factor_identity (f : Signature K n)
    (small : Signature.TensorClosure (fun m (_ : Signature K m)=>m≤2) f)
    (i j : Fin n) (different : i≠j) (edge : I.minor f i j≠0) (x : Fin n→Bool) :
    f x*f (fun _=>false)=f (pair i j (x i) (x j))*f (outside i j x) := by
  obtain ⟨D,hs,rfl⟩:=small
  exact factor_identity D hs i j different (I.same_block_of_minor D i j edge) x

theorem cap_pair (f : Signature K n) (i j k : Fin n) (ik : i≠k) (jk : j≠k) (a b : Bool) :
    P.cap k f (pair i j a b)=f (pair i j a b) := by
  unfold P.cap
  congr 1
  funext l
  by_cases hl : l=k
  · subst l
    simp [pair,Ne.symm ik,Ne.symm jk]
  · simp [hl]

theorem common_cap_factor (f : Signature K n)
    (caps : ∀k,Signature.TensorClosure (fun m (_ : Signature K m)=>m≤2) (P.cap k f))
    (i j k : Fin n) (different : i≠j) (ik : i≠k) (jk : j≠k)
    (edge : I.minor f i j≠0) (x : Fin n→Bool) :
    P.cap k f x*f (fun _=>false)=f (pair i j (x i) (x j))*P.cap k f (outside i j x) := by
  have h:=small_factor_identity (P.cap k f) (caps k) i j different
    (by rw [I.cap_minor f i j k ik jk];exact edge) x
  simpa only [P.cap_origin,cap_pair f i j k ik jk] using h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryFactor
end
