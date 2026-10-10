import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinComplete
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPairedTerminal

/-! Every concrete sourced unary endpoint is consumed by its proved terminal.
No source-selection backend or assumed independent-unary hardness remains. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryTerminalComplete
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false

theorem countingHard (source : GlobalCloseCompletionUnaryStructuralSource.Completion G) :
    NoXWeightedAntiResourcesOriginal.Hard G := by
  cases source with
  | ternary src=>exact GlobalCloseCompletionIndependentPinsTernaryComplete.structural G src
  | paired src N support det=>exact GlobalCloseCompletionUnaryPairedTerminal.countingHard G src N support det
  | pins src negative resource=>exact GlobalCloseCompletionUnaryBothPinComplete.countingHard G src resource negative

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryTerminalComplete
end
