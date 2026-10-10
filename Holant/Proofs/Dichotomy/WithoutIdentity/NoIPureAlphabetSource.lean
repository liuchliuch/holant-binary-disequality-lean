import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureAlphabetData
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePinsSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureXGraph
import Holant.Proofs.Dichotomy.Native.NativeNormalizedGraphAdjoin

/-! Actual pure Eq4 gives a retained exact native alphabet with literal
Eq4, both pins and X, together with its controlled original-oracle source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureAlphabetSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.EightVertex.ProductAnchor
namespace A
export NativeNormalizedGraphAdjoin (signatures old old_literal newLabel normalized_literal source lift)
end A
namespace M
export GlobalCloseCompletionUnaryDescentSource (ambient)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (arity i.val)) (F : FixedField L degree)
variable (pure : GlobalCloseCompletionComplementQ4ClassificationBlocks.Pure H)

def produce : NoIPureAlphabetData.Data L H F := by
  classical
  apply Classical.choice
  obtain ⟨N,c,cn,form⟩:=pure
  let J:=A.signatures F H N c
  let e:=A.newLabel H
  have eq4 : (⟨NativeNormalizedGraphAdjoin.arity H N e.val,J e⟩ : AnySignature L)=⟨4,equalityFour⟩ :=
    A.normalized_literal F H N c equalityFour cn form
  have row : N.network.denote=GlobalCloseCompletionComplementQ4Series.row c 0 0 0 :=
    form.trans (GlobalCloseCompletionComplementQ4ClassificationBlocks.pure_row c).symm
  let X:=A.lift F H N c (NoIPureXGraph.output H N)
  have xv : X.network.denote=fun x=>c^2*Signature.disequality (x 0) (x 1) :=NoIPureXGraph.value H N c row
  let J2:=A.signatures F J X (c^2)
  let e2:=A.old J e
  let x2:=A.newLabel J
  have eq42 : (⟨NativeNormalizedGraphAdjoin.arity J X e2.val,J2 e2⟩ : AnySignature L)=⟨4,equalityFour⟩ :=
    (A.old_literal F J X (c^2) e).trans eq4
  have flip2 : (⟨NativeNormalizedGraphAdjoin.arity J X x2.val,J2 x2⟩ : AnySignature L)=
      ⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩ :=
    A.normalized_literal F J X (c^2) _ (pow_ne_zero _ cn) xv
  have qp : PureEquality (RingHomRealization.mapSignature L.subtype (equalityFour : Signature L 4)) := by
    refine ⟨1,1,one_ne_zero,one_ne_zero,?_⟩
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp [RingHomRealization.mapSignature,equalityFour,ge4,complementWord,funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]
  let D:=NoIPurePinsSource.produce L J2 F equalityFour e2 eq42 qp
  letI : Algebra ℚ D.K:=D.K.algebra'
  have old : M.ambient L H⊆M.ambient L J2 := by
    rintro f ⟨i,rfl⟩
    exact ⟨A.old J (A.old H i),congrArg (RingHomRealization.mapAny L.subtype)
      ((A.old_literal F J X (c^2) (A.old H i)).trans (A.old_literal F H N c i))⟩
  have emem : (⟨4,equalityFour⟩ : AnySignature AlgebraicComplex)∈M.ambient D.K D.table := by
    apply D.retained
    exact ⟨e2,(congrArg (RingHomRealization.mapAny L.subtype) eq42).trans (NoIPureAlphabetData.map_eq4 (K:=L) L.subtype)⟩
  have xmem : (⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩ : AnySignature AlgebraicComplex)∈M.ambient D.K D.table := by
    apply D.retained
    exact ⟨x2,(congrArg (RingHomRealization.mapAny L.subtype) flip2).trans (NoIPureAlphabetData.map_x (K:=L) L.subtype)⟩
  obtain ⟨ei,he⟩:=emem
  obtain ⟨xi,hx⟩:=xmem
  exact ⟨{
    K:=D.K
    degree:=D.degree
    presentation:=D.presentation
    count:=D.count
    arity:=D.arity
    table:=D.table
    retained:=old.trans D.retained
    pin:=D.pin
    pin_literal:=D.pin_literal
    q:=D.q
    label:=D.label
    literal:=D.literal
    pure:=D.pure
    source:=Programme.compose D.source (Programme.compose (A.source F J X (c^2) (pow_ne_zero _ cn)) (A.source F H N c cn))
    equality:=ei
    equality_literal:=NoIPureAlphabetData.map_injective (K:=D.K) D.K.subtype (he.trans (NoIPureAlphabetData.map_eq4 (K:=D.K) D.K.subtype).symm)
    flip:=xi
    flip_literal:=NoIPureAlphabetData.map_injective (K:=D.K) D.K.subtype (hx.trans (NoIPureAlphabetData.map_x (K:=D.K) D.K.subtype).symm) }⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureAlphabetSource
end
