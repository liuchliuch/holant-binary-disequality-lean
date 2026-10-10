import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPairedReceipt
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesAnchor
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryTraceTerminal

/-! The paired endpoint of the whole-family unary selector closes at the
original input. Its genuine Eq4 receipt retains the charted old Z as a
nonsingular symmetric trace-zero row; exact anchor and pin sources precede
the already strict full-family trace consumer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPairedTerminal
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export GlobalCloseCompletionUnaryStructuralSource (PinSource)
end S
namespace Q
export GlobalCloseCompletionUnaryQuaternaryForm (Paired determinant)
end Q
namespace R
export GlobalCloseCompletionUnaryPairedReceipt (receipt old_included)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : S.PinSource G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (N : NoXOrdinaryGraphAdjoin.Output src.table 4)
variable (support : Q.Paired N.network.denote) (det : Q.determinant N.network.denote≠0)

abbrev anchor := GlobalCloseCompletionPairedSeriesAnchor.input G src.K src.table src.F
  (R.receipt G src N support det) src.toOriginal
abbrev data := GlobalCloseCompletionOrdinaryAnchorPins.data G (anchor G src N support det)

theorem old_included : GlobalCloseCompletionUnaryDescentSource.ambient src.K src.table⊆
    GenericOrdinarySource.family G (data G src N support det) :=
  (R.old_included G src N support det).trans
    (GlobalCloseCompletionOrdinaryAnchorPins.old_included G (anchor G src N support det))

include src N support det in
theorem countingHard : NoXWeightedAntiResourcesOriginal.Hard G := by
  have resource:=(GlobalCloseCompletionUnaryStructuralSource.PinSource.resource G src).mono
    (old_included G src N support det)
  rcases GlobalCloseCompletionUnaryTraceTerminal.classified G (data G src N support det) resource with tract|hard
  · exact False.elim (src.negative (tract.mono_family (old_included G src N support det)))
  · exact hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPairedTerminal
end
