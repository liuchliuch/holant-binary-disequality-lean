import Holant.Proofs.Dichotomy.Main.PaperControlledTernary
import Holant.Proofs.Dichotomy.Main.PaperControlledUnaryPaired
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinComplete

/-! Every actual unary structural source is consumed without forgetting its
counted-verifier programme's query and answer control. The strict universal
prime and both-pin projection selectors are reused unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledUnary
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G

variable (src : GlobalCloseCompletionIndependentPinsSource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'

theorem bothPinHard
    (resource : GlobalCloseCompletionUnaryTraceOrX.Witness (GlobalCloseCompletionIndependentPinsSource.family G src))
    (negative : ¬Tract (GlobalCloseCompletionIndependentPinsSource.family G src)) :
    PaperControlledHardness.Original G := by
  cases GlobalCloseCompletionUnaryBothPinSelector.produce src.K src.H
    (GlobalCloseCompletionUnaryBothPinComplete.pin G src)
    (GlobalCloseCompletionUnaryBothPinComplete.pin_value G src) negative with
  | ternary N prime=>exact PaperControlledTernary.countingHard G src N prime resource negative
  | paired result=>
    exact PaperControlledUnaryPaired.independent G src
      result.graph result.matrix result.form result.nonsingular negative

theorem countingHard (source : GlobalCloseCompletionUnaryStructuralSource.Completion G) :
    PaperControlledHardness.Original G := by
  cases source with
  | ternary chart=>exact PaperControlledTernary.structural G chart
  | paired chart N support det=>exact PaperControlledUnaryPaired.countingHard G chart N support det
  | pins table negative resource=>exact bothPinHard G table resource negative

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledUnary
end
