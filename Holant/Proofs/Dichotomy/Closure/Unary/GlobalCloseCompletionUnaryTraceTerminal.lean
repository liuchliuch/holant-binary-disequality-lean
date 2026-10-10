import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryTraceOrX
import Holant.Proofs.Dichotomy.Closure.Ambient.GlobalCloseCompletionAmbientTrace

/-! The retained symmetric trace-zero or literal-X resource closes an
actual ordinary Eq4/two-pin table by the strict full-family consumer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryTraceTerminal
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export GlobalCloseCompletionUnaryTraceOrX (Witness)
end W
namespace T
export GlobalCloseCompletionSymmetricGHZTrace (binary)
end T
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : GenericOrdinarySource.Data G)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false

theorem classified (w : W.Witness (GenericOrdinarySource.family G src)) :
    Tract (GenericOrdinarySource.family G src) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  cases w with
  | trace a b member det=>exact GlobalCloseCompletionAmbientTrace.classified G src a b b member det
  | x member=>
    have equal : (T.binary (0 : AlgebraicComplex) 1 1)=xAnchor := by
      funext x
      cases h0 : x 0 <;>cases h1 : x 1 <;>
        simp [T.binary,xAnchor,kernelSignature,Signature.disequality,h0,h1]
    rw [←equal] at member
    exact GlobalCloseCompletionAmbientTrace.classified G src 0 1 1 member (by norm_num)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryTraceTerminal
end
