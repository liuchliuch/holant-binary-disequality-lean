import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryStructuralSource
import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopUnaryCurrent

/-! The retained-unary structural stop reaches the actual universal unary
source producer. The whole current table and saved original-G reduction are
used directly. Remaining consumers see only sourced ternary, paired-q4, or
literal two-pin instances, never the old small-endpoint or independent-row
residuals. This is a source theorem, not a hardness assertion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopUnarySource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace O
export GlobalCloseCompletionStopOrdinarySource (field presentation table family toOriginal z_member tract_iff_current)
end O
namespace U
export GlobalCloseCompletionStopUnaryCurrent (graph labels exact ordinary graph_nonzero)
end U
namespace S
export GlobalCloseCompletionUnaryStructuralSource (Completion unary)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (P : Palette G)
local instance : Algebra ℚ (O.field G P):=(O.field G P).algebra'
variable (u : Signature (OI.K G) 1) (retained : (⟨1,u⟩ : AnySignature (OI.K G))∈P.family)

def actual : NoXOrdinaryGraphAdjoin.Output (O.table G P) 1 :=
  ⟨U.graph G P u retained,U.labels G P u retained,U.exact G P u retained,U.ordinary G P u retained⟩

inductive Completion : Type 1 where
  | tract (criterion : TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G P)))
  | source (data : S.Completion G)

def complete : Completion G P := by
  classical
  by_cases tract : Tract (O.family G P)
  · exact .tract ((O.tract_iff_current G P).mp tract)
  · exact .source (S.unary G (O.field G P) (O.presentation G P) (O.table G P) (O.toOriginal G P)
      (actual G P u retained) tract (U.graph_nonzero G P u retained) (O.z_member G P))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopUnarySource
end
