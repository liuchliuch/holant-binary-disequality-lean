import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinary
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPairedTerminal
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsPairedComplete

/-! Paired structural endpoints retain the actual counting source control.
The strict paired-series graph and source record are reused verbatim; the
universal ordinary terminal consumes the full extended family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledUnaryPaired
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G

section Chart
variable (src : GlobalCloseCompletionUnaryStructuralSource.PinSource G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (N : NoXOrdinaryGraphAdjoin.Output src.table 4)
variable (support : GlobalCloseCompletionUnaryQuaternaryForm.Paired N.network.denote)
variable (det : GlobalCloseCompletionUnaryQuaternaryForm.determinant N.network.denote≠0)
include src N support det in
theorem countingHard : PaperControlledHardness.Original G := by
  apply PaperControlledOrdinary.countingHard G
    (GlobalCloseCompletionUnaryPairedTerminal.data G src N support det)
  intro tract
  exact src.negative (tract.mono_family
    (GlobalCloseCompletionUnaryPairedTerminal.old_included G src N support det))
end Chart

section Independent
variable (src : GlobalCloseCompletionIndependentPinsSource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (N : Macro src.H 4) (B : Matrix Bool Bool src.K)
variable (form : N.network.denote=GlobalCloseCompletionPairedSeriesCore.row B) (det : B.det≠0)
include N B form det in
theorem independent (negative : ¬Tract (GlobalCloseCompletionIndependentPinsSource.family G src)) :
    PaperControlledHardness.Original G := by
  apply PaperControlledOrdinary.countingHard G
    (GlobalCloseCompletionIndependentPinsPairedComplete.data G src N B form det)
  intro tract
  exact negative (tract.mono_family
    (GlobalCloseCompletionIndependentPinsPairedComplete.old_included G src N B form det))
end Independent


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledUnaryPaired
end
