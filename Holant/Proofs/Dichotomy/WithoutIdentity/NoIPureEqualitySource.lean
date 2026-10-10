import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureEqualityCap
import Holant.Proofs.Dichotomy.WithoutIdentity.NoISuppliedIdentityConsumer

/-! The genuine diagonal-cofactor and full-unary exits of the pure-q4 source.
The whole old alphabet and its exact native-X oracle remain in the conclusion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureEqualitySource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace A
export NativeNormalizedGraphAdjoin (signatures old old_literal newLabel normalized_literal source)
end A
namespace C
export NoIPureEqualityCap (pure cap cap_value unaryCap unary_value)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {s degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (arity i.val)) (F : FixedField L degree)

def diagonal (N : NativeAntiTargetSource.Output H 2) (p q : L) (pn : p≠0) (qn : q≠0)
    (form : N.network.denote=binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal p q)) :
    NoISuppliedIdentityData.Data L H F := by
  let J:=A.signatures F H N 1
  let j:=A.newLabel H
  have literal : (⟨NativeNormalizedGraphAdjoin.arity H N j.val,J j⟩ : AnySignature L)=
      ⟨2,binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal p q)⟩ :=
    A.normalized_literal F H N 1 _ one_ne_zero (by simpa using form)
  let D:=NoIWeightedEqualitySource.produce L J F j p q pn qn literal
  have old : GlobalCloseCompletionUnaryDescentSource.ambient L H⊆
      GlobalCloseCompletionUnaryDescentSource.ambient L J := by
    rintro f ⟨i,rfl⟩
    exact ⟨A.old H i,congrArg (RingHomRealization.mapAny L.subtype) (A.old_literal F H N 1 i)⟩
  exact {
    K:=D.K
    degree:=D.degree
    presentation:=D.presentation
    count:=D.count
    b:=D.b
    table:=D.table
    identity:=D.identity
    identity_literal:=D.identity_literal
    basis:=D.basis
    native:=D.native
    retained:=(Set.image_mono old).trans D.retained
    source:=Programme.compose D.source (A.source F H N 1 one_ne_zero) }

def cofactor (Q : NativeAntiTargetSource.Output H 4) (B : NativeAntiTargetSource.Output H 2)
    (p q : L) (pn : p≠0) (qn : q≠0) (form : Q.network.denote=C.pure p q)
    (top : B.network.denote (fun _=>false)≠0) (bottom : B.network.denote (fun _=>true)≠0) :
    NoISuppliedIdentityData.Data L H F :=
  diagonal L H F (C.cap H Q B) (p*B.network.denote (fun _=>true)) (q*B.network.denote (fun _=>false))
    (mul_ne_zero pn bottom) (mul_ne_zero qn top) (C.cap_value H Q B p q form)

def unary (Q : NativeAntiTargetSource.Output H 4) (U : NativeAntiTargetSource.Output H 1)
    (p q : L) (pn : p≠0) (qn : q≠0) (form : Q.network.denote=C.pure p q)
    (top : U.network.denote (fun _=>false)≠0) (bottom : U.network.denote (fun _=>true)≠0) :
    NoISuppliedIdentityData.Data L H F :=
  diagonal L H F (C.unaryCap H Q U) (p*(U.network.denote (fun _=>true))^2) (q*(U.network.denote (fun _=>false))^2)
    (mul_ne_zero pn (pow_ne_zero _ bottom)) (mul_ne_zero qn (pow_ne_zero _ top)) (C.unary_value H Q U p q form)

theorem cofactor_classified (Q : NativeAntiTargetSource.Output H 4) (B : NativeAntiTargetSource.Output H 2)
    (p q : L) (pn : p≠0) (qn : q≠0) (form : Q.network.denote=C.pure p q)
    (top : B.network.denote (fun _=>false)≠0) (bottom : B.network.denote (fun _=>true)≠0) :
    Tract (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient L H)) ∨
      (NoISuppliedIdentityConsumer.target L H F).Hard :=
  NoISuppliedIdentityConsumer.tract_or_hard L H F (cofactor L H F Q B p q pn qn form top bottom)

theorem unary_classified (Q : NativeAntiTargetSource.Output H 4) (U : NativeAntiTargetSource.Output H 1)
    (p q : L) (pn : p≠0) (qn : q≠0) (form : Q.network.denote=C.pure p q)
    (top : U.network.denote (fun _=>false)≠0) (bottom : U.network.denote (fun _=>true)≠0) :
    Tract (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient L H)) ∨
      (NoISuppliedIdentityConsumer.target L H F).Hard :=
  NoISuppliedIdentityConsumer.tract_or_hard L H F (unary L H F Q U p q pn qn form top bottom)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureEqualitySource
end
