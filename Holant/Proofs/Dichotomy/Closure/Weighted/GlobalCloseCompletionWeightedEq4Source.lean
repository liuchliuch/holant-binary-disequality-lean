import Holant.Proofs.Dichotomy.Closure.Weighted.GlobalCloseCompletionWeightedEq4Normalization
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorPins

/-! An actual weighted ordinary Eq4 receives one unconditional full-family
Eq4/two-pin source to unchanged original G. Finite versus infinite weight
ratio, exact normalization, field transport and pin installation are internal.
Every original ordinary row is retained literally in algebraic coordinates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionWeightedEq4Source
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export GlobalCloseCompletionWeightedEq4Normalization (Input family produce)
end W
namespace Pn
export GlobalCloseCompletionOrdinaryAnchorPins (data old_included)
end Pn
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (D : W.Input G)

def data : GenericOrdinarySource.Data G := Pn.data G (W.produce G D).output

theorem old_included : W.family G D⊆GenericOrdinarySource.family G (data G D) :=
  (W.produce G D).included.trans (Pn.old_included G (W.produce G D).output)

theorem obstruction (negative : ¬Tract (W.family G D)) :
    StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G (data G D))) := by
  apply (GenericOrdinarySource.rejected_iff G (data G D)).mp
  intro tract
  exact negative (tract.mono_family (old_included G D))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionWeightedEq4Source
end
