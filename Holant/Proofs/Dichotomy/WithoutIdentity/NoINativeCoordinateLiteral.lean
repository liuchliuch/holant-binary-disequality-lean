import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeCoordinateSource

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeCoordinateLiteral
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
namespace C
export NoINativeCoordinateSource (field table table_value)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {r : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin r)→Signature L (arity i.val)) (R : InvertibleKernel)

theorem literal (i : Fin r) :
    RingHomRealization.mapAny (C.field L H R).subtype
      (⟨arity i.val,C.table L H R i⟩ : AnySignature (C.field L H R))=
      ⟨arity i.val,R.symm.action (fun x=>(H i x : AlgebraicComplex))⟩ :=
  congrArg (fun f : Signature AlgebraicComplex (arity i.val)=>(⟨arity i.val,f⟩ : AnySignature AlgebraicComplex))
    (funext (C.table_value L H R i))

theorem retained {n : ℕ} (i : Fin r) (f : Signature AlgebraicComplex n)
    (old : RingHomRealization.mapAny L.subtype (⟨arity i.val,H i⟩ : AnySignature L)=⟨n,f⟩) :
    RingHomRealization.mapAny (C.field L H R).subtype
      (⟨arity i.val,C.table L H R i⟩ : AnySignature (C.field L H R))=⟨n,R.symm.action f⟩ :=
  (literal L H R i).trans (congrArg
    (fun g : AnySignature AlgebraicComplex=>(⟨g.1,R.symm.action g.2⟩ : AnySignature AlgebraicComplex)) old)

theorem included : familyAction R.symm (GlobalCloseCompletionUnaryDescentSource.ambient L H)⊆
    GlobalCloseCompletionUnaryDescentSource.ambient (C.field L H R) (C.table L H R) := by
  rintro f ⟨g,⟨i,rfl⟩,rfl⟩
  exact ⟨i,literal L H R i⟩

theorem lift_identity {K : Type} [Field K] (phi : K→+*AlgebraicComplex)
    (f : AnySignature K) (scalar : AlgebraicComplex) (nonzero : scalar≠0)
    (form : RingHomRealization.mapAny phi f=⟨2,fun x=>scalar*Signature.equality (x 0) (x 1)⟩) :
    ∃c : K,c≠0 ∧ phi c=scalar ∧ f=⟨2,fun x=>c*Signature.equality (x 0) (x 1)⟩ := by
  obtain ⟨n,f⟩:=f
  have hn : n=2:=congrArg Sigma.fst form
  subst n
  have hf : RingHomRealization.mapSignature phi f=(fun x=>scalar*Signature.equality (x 0) (x 1)):=
    eq_of_heq (Sigma.mk.inj_iff.mp form).2
  let c:=f (fun _=>false)
  have hc : phi c=scalar:=by simpa [c,RingHomRealization.mapSignature,Signature.equality] using congrFun hf (fun _=>false)
  refine ⟨c,(fun zero=>nonzero (by rw [←hc,zero,map_zero])),hc,?_⟩
  apply congrArg (fun g : Signature K 2=>(⟨2,g⟩ : AnySignature K))
  funext x
  apply phi.injective
  have h:=congrFun hf x
  change phi (f x)=_ at h
  rw [h,map_mul,hc]
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [Signature.equality,h0,h1]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeCoordinateLiteral
end
