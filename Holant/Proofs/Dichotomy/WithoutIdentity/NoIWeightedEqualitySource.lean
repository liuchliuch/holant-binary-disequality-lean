import Holant.Proofs.Dichotomy.WithoutIdentity.NoISuppliedIdentityData
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIWeightedEqualityFrame
import Holant.Proofs.Dichotomy.Native.NativeNormalizedGraphAdjoin
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetExtension

/-! Literal nonsingular weighted equality supplies an actual native-I source
for the complete old alphabet. One common coordinate change preserves X,
then the exact scalar-normalization compiler installs I. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIWeightedEqualitySource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export NoIWeightedEqualityFrame (Frame produce signature)
end W
namespace C
export NoINativeCoordinateSource (field presentation table controlled)
export NoINativeCoordinateLiteral (retained included lift_identity)
end C
namespace A
export NativeNormalizedGraphAdjoin (arity signatures old old_literal newLabel normalized_literal source)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {r degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin r)→Signature L (arity i.val)) (F : FixedField L degree)
variable (j : Fin r) (a b : L) (ha : a≠0) (hb : b≠0)
variable (literal : (⟨arity j.val,H j⟩ : AnySignature L)=
  ⟨2,binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal a b)⟩)

include literal in
theorem mapped : RingHomRealization.mapAny L.subtype (⟨arity j.val,H j⟩ : AnySignature L)=
    ⟨2,W.signature (a : AlgebraicComplex) (b : AlgebraicComplex)⟩ := by
  rw [literal]
  apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [RingHomRealization.mapSignature,binarySignature,OrdinaryTargetInterpolationDiagonal.diagonal,
      W.signature,GlobalCloseCompletionSymmetricGHZFrame.diagonal,h0,h1] <;> rfl

def produce : NoISuppliedIdentityData.Data L H F := by
  classical
  apply Classical.choice
  have ha' : (a : AlgebraicComplex)≠0:=fun zero=>ha (Subtype.ext zero)
  have hb' : (b : AlgebraicComplex)≠0:=fun zero=>hb (Subtype.ext zero)
  let W:=W.produce (a : AlgebraicComplex) (b : AlgebraicComplex) ha' hb'
  let K:=C.field L H W.B
  letI : Algebra ℚ K:=K.algebra'
  let F2:=C.presentation L H W.B
  let J:=C.table L H W.B
  have hl : RingHomRealization.mapAny K.subtype (⟨arity j.val,J j⟩ : AnySignature K)=
      ⟨2,fun x=>W.scalar*Signature.equality (x 0) (x 1)⟩ :=
    (C.retained L H W.B j _ (mapped L H j a b literal)).trans
      (congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex)) W.row)
  obtain ⟨c,hc,hvalue,he⟩:=C.lift_identity K.subtype ⟨arity j.val,J j⟩ W.scalar W.nonzero hl
  let N:=NativeAntiTargetExtension.row J j (fun x=>c*Signature.equality (x 0) (x 1)) he
  have form : N.network.denote=(fun x=>c*Signature.equality (x 0) (x 1)):=Network.denote_corolla _
  have kept : GlobalCloseCompletionUnaryDescentSource.ambient K J⊆
      GlobalCloseCompletionUnaryDescentSource.ambient K (A.signatures F2 J N c) := by
    rintro f ⟨i,rfl⟩
    exact ⟨A.old J i,congrArg (RingHomRealization.mapAny K.subtype) (A.old_literal F2 J N c i)⟩
  exact ⟨{
    K:=K
    degree:=_
    presentation:=F2
    count:=r+1
    b:=A.arity J N
    table:=A.signatures F2 J N c
    identity:=A.newLabel J
    identity_literal:=A.normalized_literal F2 J N c _ hc form
    basis:=W.B
    native:=W.edge
    retained:=(C.included L H W.B).trans kept
    source:=Programme.compose (A.source F2 J N c hc) (C.controlled L F H W.B W.edge) }⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIWeightedEqualitySource
end
