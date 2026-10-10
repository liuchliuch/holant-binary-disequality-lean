import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZSource
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWGeneralCore
import Holant.Proofs.Closure.ClosureFactorTreeAction

/-! Independent invertible changes at the three ternary ports preserve
the actual tensor-primality predicate. This is semantic orbit algebra only;
none of the three matrices is asserted to be a physical gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernaryAction
open Holant Holant.Tractable Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open scoped BigOperators
namespace Q
export GlobalCloseCompletionSymmetricGHZCoordinates (eq3)
end Q
namespace W
export GlobalCloseCompletionIndependentPinsWCore (w)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false

theorem prime_action {n : ℕ} (f : Signature AlgebraicComplex n)
    (prime : Prime (⟨n,f⟩ : AnySignature AlgebraicComplex)) (A : Fin n→InvertibleKernel) :
    Prime (⟨n,Signature.coordinateAction (fun i=>(A i).matrix) f⟩ : AnySignature AlgebraicComplex) := by
  let inv : Fin n→Kernel AlgebraicComplex:=fun i=>(A i).inverse
  have cancellation : Signature.coordinateAction inv
      (Signature.coordinateAction (fun i=>(A i).matrix) f)=f :=
    Signature.coordinateAction_cancel _ _ (fun i=>(A i).inverse_matrix) f
  constructor
  · intro zero
    change Signature.coordinateAction (fun i=>(A i).matrix) f=0 at zero
    rw [zero,Signature.coordinateAction_zero] at cancellation
    exact prime.1 cancellation.symm
  · rintro ⟨l,r,⟨split⟩⟩
    let left : AnySignature AlgebraicComplex:=⟨l.1,
      Signature.coordinateAction (fun i=>inv (split.ports (.inl i))) l.2⟩
    let right : AnySignature AlgebraicComplex:=⟨r.1,
      Signature.coordinateAction (fun i=>inv (split.ports (.inr i))) r.2⟩
    apply prime.2
    refine ⟨left,right,⟨{
      left_pos:=split.left_pos
      right_pos:=split.right_pos
      ports:=split.ports
      scale:=split.scale
      equation:=?_ }⟩⟩
    have h:=congrArg (Signature.coordinateAction inv) split.equation
    rw [cancellation,ClosureFactorTreeAction.coordinateAction_scale] at h
    change f=(fun x=>(split.scale : AlgebraicComplex)*
      Signature.coordinateAction inv (Tensor.reindex split.ports (Tensor.tensor l.2 r.2)) x) at h
    rw [ClosureFactorTreeAction.coordinateAction_tensor] at h
    exact h

def ports (A B C : InvertibleKernel) : Fin 3→InvertibleKernel := ![A,B,C]
def action (A B C : InvertibleKernel) (f : Signature AlgebraicComplex 3) : Signature AlgebraicComplex 3 :=
  Signature.coordinateAction (fun i=>(ports A B C i).matrix) f

theorem ghz (A B C : InvertibleKernel) : action A B C Q.eq3=
    GlobalCloseCompletionTernaryGHZCore.ghz A.matrix B.matrix C.matrix := by
  funext x
  simp only [action,Signature.coordinateAction,GlobalCloseCompletionTernaryGHZAction.sum_words]
  simp [ports,Q.eq3,GlobalCloseCompletionTernaryGHZCore.ghz,Fin.prod_univ_three,Fintype.sum_bool,
    funext_iff,Fin.forall_fin_succ]

theorem w (A B C : InvertibleKernel) : action A B C W.w=
    GlobalCloseCompletionIndependentPinsWGeneralCore.image A.matrix B.matrix C.matrix := by
  funext x
  simp only [action,Signature.coordinateAction,GlobalCloseCompletionTernaryGHZAction.sum_words]
  simp [ports,W.w,GlobalCloseCompletionIndependentPinsWGeneralCore.image,Fin.prod_univ_three,Fintype.sum_bool]
  ring

theorem comp (A B C D E F : InvertibleKernel) (f : Signature AlgebraicComplex 3) :
    action A B C (action D E F f)=action (A.comp D) (B.comp E) (C.comp F) f := by
  unfold action
  rw [Signature.coordinateAction_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem inverse (A B C : InvertibleKernel) (f : Signature AlgebraicComplex 3) :
    action A.symm B.symm C.symm (action A B C f)=f := by
  apply Signature.coordinateAction_cancel
  intro i
  fin_cases i
  · exact A.inverse_matrix
  · exact B.inverse_matrix
  · exact C.inverse_matrix

def Orbit (f : Signature AlgebraicComplex 3) : Prop :=
  (∃A B C : InvertibleKernel,f=action A B C Q.eq3) ∨
  (∃A B C : InvertibleKernel,f=action A B C W.w)

theorem orbit_action (A B C : InvertibleKernel) (f : Signature AlgebraicComplex 3) (h : Orbit f) :
    Orbit (action A B C f) := by
  rcases h with ⟨D,E,F,h⟩|⟨D,E,F,h⟩
  · exact Or.inl ⟨A.comp D,B.comp E,C.comp F,by rw [h,comp]⟩
  · exact Or.inr ⟨A.comp D,B.comp E,C.comp F,by rw [h,comp]⟩

theorem orbit_of_action (A B C : InvertibleKernel) (f : Signature AlgebraicComplex 3)
    (h : Orbit (action A B C f)) : Orbit f := by
  have h':=orbit_action A.symm B.symm C.symm _ h
  rw [inverse] at h'
  exact h'


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernaryAction
end
