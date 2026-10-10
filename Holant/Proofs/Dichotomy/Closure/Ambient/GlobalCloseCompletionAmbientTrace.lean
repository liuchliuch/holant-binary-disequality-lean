import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZTrace

/-! Transport a retained ambient trace-zero row through any exact coefficient
field extension. This only reads the literal row already in the full source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionAmbientTrace
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace T
export GlobalCloseCompletionSymmetricGHZTrace (binary classified)
end T
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (row row_denote)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false

private theorem lift {K : Type} [Field K] (phi : K→+*AlgebraicComplex)
    (f : AnySignature K) (a b c : AlgebraicComplex)
    (literal : RingHomRealization.mapAny phi f=⟨2,T.binary a b c⟩)
    (det : -a^2-b*c≠0) :
    ∃u v w : K, f=⟨2,T.binary u v w⟩ ∧ -u^2-v*w≠0 := by
  obtain ⟨n,f⟩:=f
  have hn : n=2:=congrArg Sigma.fst literal
  subst n
  have hf : RingHomRealization.mapSignature phi f=T.binary a b c:=
    eq_of_heq (Sigma.mk.inj_iff.mp literal).2
  let u:=f ![false,false]
  let v:=f ![false,true]
  let w:=f ![true,false]
  have hu : phi u=a:=by simpa [u,RingHomRealization.mapSignature,T.binary] using congrFun hf ![false,false]
  have hv : phi v=b:=by simpa [v,RingHomRealization.mapSignature,T.binary] using congrFun hf ![false,true]
  have hw : phi w=c:=by simpa [w,RingHomRealization.mapSignature,T.binary] using congrFun hf ![true,false]
  refine ⟨u,v,w,?_,?_⟩
  · apply congrArg (fun g : Signature K 2=>(⟨2,g⟩ : AnySignature K))
    funext x
    apply phi.injective
    have hx:=congrFun hf x
    change phi (f x)=_ at hx
    rw [hx]
    cases h0 : x 0 <;> cases h1 : x 1 <;> simp [T.binary,h0,h1,hu,hv,hw]
  · intro he
    apply det
    simpa [hu,hv,hw] using congrArg phi he

variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'

theorem classified (a b c : AlgebraicComplex)
    (member : (⟨2,T.binary a b c⟩ : AnySignature AlgebraicComplex)∈GenericOrdinarySource.family G src)
    (det : -a^2-b*c≠0) :
    Tract (GenericOrdinarySource.family G src) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  obtain ⟨j,hj⟩:=member
  obtain ⟨u,v,w,hl,hd⟩:=lift src.K.subtype ⟨src.b j.val,src.H j⟩ a b c hj det
  exact T.classified G src (M.row j (T.binary u v w) hl) u v w (M.row_denote _ _ _) hd
theorem of_matrix (B : Matrix Bool Bool AlgebraicComplex)
    (member : (⟨2,Holant.Complexity.BinaryInterpolation.Chains.binarySignature B⟩ :
      AnySignature AlgebraicComplex)∈GenericOrdinarySource.family G src)
    (trace : Matrix.trace B=0) (det : B.det≠0) :
    Tract (GenericOrdinarySource.family G src) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  have same : B true true= -B false false := by
    simp [Matrix.trace] at trace
    linear_combination trace
  have form : Holant.Complexity.BinaryInterpolation.Chains.binarySignature B=
      T.binary (B false false) (B false true) (B true false) := by
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [Holant.Complexity.BinaryInterpolation.Chains.binarySignature,T.binary,h0,h1,same]
  rw [form] at member
  apply classified G src _ _ _ member
  intro zero
  apply det
  rw [Holant.Complexity.BinaryInterpolation.det_entries,same]
  linear_combination zero


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionAmbientTrace
end
