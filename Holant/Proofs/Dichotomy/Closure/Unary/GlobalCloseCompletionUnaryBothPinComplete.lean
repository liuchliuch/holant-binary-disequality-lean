import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinSelector
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsTernaryComplete
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsPairedComplete

/-! The sourced both-pin terminal has no supplied classifier. Its internal
least-prime projection selector constructs a real ternary or paired graph,
and the corresponding strict full-family source closes original-G hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinComplete
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export GlobalCloseCompletionIndependentPinsSource (Data family)
end S
namespace W
export GlobalCloseCompletionUnaryTraceOrX (Witness)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : S.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'

def pin (v : Bool) : NoXOrdinaryGraphAdjoin.Output src.H 1 where
  network:=Network.corolla (QuaternaryUnaryAccess.pin v)
  labels:={vertex _:=src.p v,vertex_arity _:=congrArg Sigma.fst (src.hp v),edge e:=Fin.elim0 e}
  exact _:=src.hp v
  ordinary e:=Fin.elim0 e

theorem pin_value (v : Bool) : (pin G src v).network.denote=QuaternaryUnaryAccess.pin v := Network.denote_corolla _

theorem countingHard (resource : W.Witness (S.family G src)) (negative : ¬Tract (S.family G src)) :
    NoXWeightedAntiResourcesOriginal.Hard G := by
  cases GlobalCloseCompletionUnaryBothPinSelector.produce src.K src.H (pin G src) (pin_value G src) negative with
  | ternary N prime=>exact GlobalCloseCompletionIndependentPinsTernaryComplete.countingHard G src N prime resource negative
  | paired result=>
    exact GlobalCloseCompletionIndependentPinsPairedComplete.countingHard G src
      result.graph result.matrix result.form result.nonsingular resource negative

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinComplete
end
