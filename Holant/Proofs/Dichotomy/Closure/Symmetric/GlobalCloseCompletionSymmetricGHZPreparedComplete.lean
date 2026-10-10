import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZPrepared
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZNormalized

/-! Complete whole-family classification after the actual regular-cap
selection. All graphs, field extensions, and oracle programmes are built
inside the theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZPreparedComplete
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization OrdinaryNegativeCubicGadgets
namespace P
export GlobalCloseCompletionSymmetricGHZPrepared
  (field presentation table source ambient included retained ternary ternary_value gramGraph gram_value gram_member)
end P
namespace C
export GlobalCloseCompletionSymmetricGHZCapGraph (cap symmetric)
export GlobalCloseCompletionSymmetricGHZCapSelection (Semisimple)
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz)
end C
namespace Rt
export GlobalCloseCompletionSymmetricGHZRootInverse (produce)
end Rt
namespace S
export GlobalCloseCompletionSymmetricGHZSemantics (output frame trace_zero det_nonzero)
end S
namespace Row
export GlobalCloseCompletionSymmetricGHZRows (row value weighted series_mapped)
end Row
namespace Gr
export GlobalCloseCompletionSymmetricGHZGram
  (transformedRow similarity row_action gram_product similarity_trace similarity_determinant)
end Gr
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (N : Macro H 3) (U : Macro H 1) (M Q : InvertibleKernel)
variable (form : RingHomRealization.mapSignature L.subtype N.network.denote=C.ghz M.matrix)
variable (qmember : (⟨2,kernelSignature Q.matrix⟩ : AnySignature AlgebraicComplex)∈
    GlobalCloseCompletionUnaryDescentSource.ambient L H)
variable (qtrace : Matrix.trace Q.matrix=0)
variable (det : Matrix.det (binaryMatrix (C.cap N U).network.denote)≠0)
variable (semisimple : C.Semisimple (binaryMatrix (C.cap N U).network.denote))

include back form qmember qtrace det semisimple in
theorem classified : Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  let C0:=S.output H (C.cap N U)
  let D:=Rt.produce L F H C0 det semisimple
  obtain ⟨R,normalized,p,q,hp,hq,weighted⟩:=S.frame L F H N U M form D det
  let K:=P.field L F H N C0 D R
  letI : Algebra ℚ K:=K.algebra'
  let T:=P.table L F H N C0 D R
  let ternary:=P.ternary L F H N C0 D R
  have ternaryValue : RingHomRealization.mapSignature (K.val.toRingHom : K→+*AlgebraicComplex) ternary.network.denote=C.symmetric p 0 0 q := by
    exact (P.ternary_value L F H N C0 D R).trans ((congrArg R.symm.action form).trans weighted)
  obtain ⟨u,v,hu,hv,shape⟩:=Row.weighted (K.val.toRingHom : K→+*AlgebraicComplex) T ternary p q hp hq ternaryValue
  have member:=P.retained L F H N C0 D R (kernelSignature Q.matrix) qmember
  obtain ⟨j,literal⟩:=member
  change RingHomRealization.mapAny (K.val.toRingHom : K→+*AlgebraicComplex)
    (⟨_,T j⟩ : AnySignature K)=⟨2,R.symm.action (kernelSignature Q.matrix)⟩ at literal
  let row:=Row.row (K.val.toRingHom : K→+*AlgebraicComplex) T j (R.symm.action (kernelSignature Q.matrix)) literal
  let gram:=P.gramGraph L F H N C0 D R normalized
  let traceGraph:=GlobalCloseCompletionSymmetricGHZInverseFinite.series T row gram
  have rowValue : RingHomRealization.mapSignature (K.val.toRingHom : K→+*AlgebraicComplex) row.network.denote=
      kernelSignature (Gr.transformedRow R Q).matrix :=
    (Row.value (K.val.toRingHom : K→+*AlgebraicComplex) T j _ literal).trans (Gr.row_action R Q)
  have graphValue : RingHomRealization.mapSignature (K.val.toRingHom : K→+*AlgebraicComplex) traceGraph.network.denote=
      kernelSignature (Gr.similarity R Q).matrix := by
    rw [←Gr.gram_product R Q]
    exact Row.series_mapped (K.val.toRingHom : K→+*AlgebraicComplex) T row gram _ _ rowValue (P.gram_value L F H N C0 D R normalized)
  have zero:=S.trace_zero (K.val.toRingHom : K→+*AlgebraicComplex) T traceGraph _ graphValue ((Gr.similarity_trace R Q).trans qtrace)
  have nonzero:=S.det_nonzero (K.val.toRingHom : K→+*AlgebraicComplex) T traceGraph _ graphValue (Gr.similarity_determinant R Q)
  exact GlobalCloseCompletionSymmetricGHZNormalized.classified
    (G:=G) (K:=K) (F:=P.presentation L F H N C0 D R) (H:=T)
    (back:=Programme.compose (P.source L F H N C0 D R normalized) back)
    (N:=ternary) (p:=u) (q:=v) (hp:=hu) (hq:=hv) (weighted:=shape)
    (Q:=traceGraph) (trace:=zero) (determinant:=nonzero)
    (original:=GlobalCloseCompletionUnaryDescentSource.ambient L H) (finite:=Set.finite_range _)
    (R:=R) (included:=P.included L F H N C0 D R) (gram:=P.gram_member L F H N C0 D R normalized)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZPreparedComplete
end
