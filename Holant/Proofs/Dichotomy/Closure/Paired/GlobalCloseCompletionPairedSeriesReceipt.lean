import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesNormalize
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesTarget

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesReceipt
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Certificates.MatchingContractionClosure
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (row row_denote)
end M
namespace A
export NoXOrdinaryGraphAdjoin (arity signatures old old_literal newLabel new_literal source)
end A
namespace P
export GlobalCloseCompletionPairedSeriesCaps (output)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)
structure Receipt where
  count : ℕ
  b : ℕ→ℕ
  table : (i : Fin count)→Signature K (b i.val)
  old : Fin s→Fin count
  old_literal : ∀i,(⟨b (old i).val,table (old i)⟩ : AnySignature K)=⟨a i.val,H i⟩
  graph : M.Macro table 4
  scalar : K
  nonzero : scalar≠0
  value : graph.network.denote=scalar • Holant.EightVertex.ProductAnchor.equalityFour
  source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 b) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F table).evaluate F)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)

def actual (N : M.Macro H 4) (c : K) (hc : c≠0)
    (hn : N.network.denote=c • Holant.EightVertex.ProductAnchor.equalityFour) : Receipt H F where
  count:=s+1
  b:=A.arity H (P.output N)
  table:=A.signatures F H (P.output N)
  old:=A.old H
  old_literal:=A.old_literal F H (P.output N)
  graph:=M.row (A.newLabel H) N.network.denote (A.new_literal F H (P.output N))
  scalar:=c
  nonzero:=hc
  value:=by rw [M.row_denote];exact hn
  source:=A.source F H (P.output N)

variable {t : ℕ} {b : ℕ→ℕ}
variable (J : (i : Fin t)→Signature K (b i.val)) (old : Fin s→Fin t)
variable (literal : ∀i,(⟨b (old i).val,J (old i)⟩ : AnySignature K)=⟨a i.val,H i⟩)
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding t 1 b) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F J).evaluate F)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F))
def compose (D : Receipt J F) : Receipt H F where
  count:=D.count
  b:=D.b
  table:=D.table
  old:=D.old ∘ old
  old_literal:=fun i=>(D.old_literal (old i)).trans (literal i)
  graph:=D.graph
  scalar:=D.scalar
  nonzero:=D.nonzero
  value:=D.value
  source:=Programme.compose D.source back


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesReceipt
end
