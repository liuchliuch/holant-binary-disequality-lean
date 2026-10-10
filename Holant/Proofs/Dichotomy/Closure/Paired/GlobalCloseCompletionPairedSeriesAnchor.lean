import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesComplete
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorPins

/-! Original-domain packaging of the proved paired source. Its scalar,
finite coefficient presentation, old alphabet and oracle programme stay exact. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesAnchor
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace R
export GlobalCloseCompletionPairedSeriesReceipt (Receipt)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K:=K.algebra'
variable {r degree : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (b i.val)) (F : FixedField K degree)
variable (D : R.Receipt H F)
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
def input : GlobalCloseCompletionOrdinaryAnchorInput.Input G where
  K:=K
  degree:=degree
  F:=F
  count:=D.count
  b:=D.b
  H:=D.table
  graph:=D.graph.network
  labels:=D.graph.labels
  exact:=D.graph.exact
  ordinary:=D.graph.edges
  scalar:=D.scalar
  nonzero:=D.nonzero
  denote:=D.value
  toOriginal:=Programme.compose D.source back

theorem old_included :
    UniversalPairReduction.FiniteFamily.family (fun i=>RingHomRealization.mapSignature K.subtype (H i)) ⊆
    UniversalPairReduction.FiniteFamily.family (fun i=>RingHomRealization.mapSignature K.subtype (D.table i)) := by
  rintro f ⟨i,rfl⟩
  exact ⟨D.old i,congrArg (RingHomRealization.mapAny K.subtype) (D.old_literal i)⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesAnchor
end
