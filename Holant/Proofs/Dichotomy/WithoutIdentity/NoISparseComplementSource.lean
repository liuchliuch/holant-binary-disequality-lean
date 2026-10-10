import Holant.Proofs.Dichotomy.WithoutIdentity.NoISparseComplementData
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetExtension

/-! A semantic complementary q4 is physically adjoined using its actual
old-family graph, then its endpoints are balanced in one common native frame.
All coefficient extensions and answer-field conversions are implemented. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace A
export NativeNormalizedGraphAdjoin (arity signatures old old_literal newLabel normalized_literal source)
end A
namespace C
export NoINativeCoordinateSource (field presentation table controlled)
export NoINativeCoordinateLiteral (retained included)
end C
namespace S
export PaperTerminalBridgeDenseSemantic (family)
export GlobalCloseCompletionComplementQ4Series (row)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)
variable (q : Signature L 4) (even : EvenSupport q)
variable (first : (entries q).a≠0) (last : (entries q).x≠0)
variable (comp : PaperTerminalBridgeComplementSign.Complement q)
variable (actual : Gadget.RealizesUpTo (S.family H) .disequality q)

def produce : NoISparseComplementData.Data L H F := by
  classical
  apply Classical.choice
  have zeroWord : (![false,false,false,false] : Fin 4→Bool)=(fun _=>false) := by funext i;fin_cases i <;> rfl
  have origin : q (fun _=>false)≠0 := by simpa only [entries,zeroWord] using first
  obtain ⟨c,hc,N,form⟩:=NoIActualEndpoint.output H q false origin actual
  let J:=A.signatures F H N c
  let j:=A.newLabel H
  have literal : (⟨A.arity H N j.val,J j⟩ : AnySignature L)=⟨4,q⟩:=A.normalized_literal F H N c q hc form
  let e:=entries q
  have an : (e.a : AlgebraicComplex)≠0:=fun zero=>first (Subtype.ext zero)
  have xn : (e.x : AlgebraicComplex)≠0:=fun zero=>last (Subtype.ext zero)
  let W:=NoIComplementFrame.produce e.a e.b e.c e.d e.x an xn
  let K:=C.field L J W.basis
  letI : Algebra ℚ K:=K.algebra'
  let F2:=C.presentation L J W.basis
  let T:=C.table L J W.basis
  have mapped : RingHomRealization.mapAny L.subtype (⟨A.arity H N j.val,J j⟩ : AnySignature L)=
      ⟨4,table ⟨(e.a : AlgebraicComplex),e.b,e.c,e.d,e.d,e.c,e.b,e.x⟩⟩ := by
    rw [literal]
    exact congrArg (fun f : Signature AlgebraicComplex 4=>(⟨4,f⟩ : AnySignature AlgebraicComplex))
      (NoISparseComplementAlgebra.mapped_form L.subtype q even comp)
  have changed : RingHomRealization.mapAny K.subtype (⟨A.arity H N j.val,T j⟩ : AnySignature K)=
      ⟨4,S.row W.scalar (e.b : AlgebraicComplex) e.c e.d⟩ :=
    (C.retained L J W.basis j _ mapped).trans
      (congrArg (fun f : Signature AlgebraicComplex 4=>(⟨4,f⟩ : AnySignature AlgebraicComplex)) W.row)
  obtain ⟨p,r,t,u,hp,hr,ht,hu,lit⟩:=NoISparseComplementAlgebra.lift_row K.subtype
    ⟨A.arity H N j.val,T j⟩ W.scalar e.b e.c e.d changed
  have pn : p≠0:=fun zero=>W.nonzero (by rw [←hp,zero,map_zero])
  have kept : GlobalCloseCompletionUnaryDescentSource.ambient L H⊆
      GlobalCloseCompletionUnaryDescentSource.ambient L J := by
    rintro f ⟨i,rfl⟩
    exact ⟨A.old H i,congrArg (RingHomRealization.mapAny L.subtype) (A.old_literal F H N c i)⟩
  exact ⟨{
    K:=K
    degree:=_
    presentation:=F2
    count:=s+1
    arity:=A.arity H N
    table:=T
    basis:=W.basis
    native:=W.native
    retained:=(Set.image_mono kept).trans (C.included L J W.basis)
    coeff:=![p,r,t,u]
    first:=pn
    graph:=NativeAntiTargetExtension.row T j (S.row p r t u) lit
    form:=Network.denote_corolla _
    source:=Programme.compose (C.controlled L F J W.basis W.native) (A.source F H N c hc) }⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementSource
end
