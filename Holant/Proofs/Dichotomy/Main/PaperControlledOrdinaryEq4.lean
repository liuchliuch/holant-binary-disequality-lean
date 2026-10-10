import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinary
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryEq4Complete

/-! A genuinely retained ordinary Eq4 graph reaches the universal controlled
ordinary terminal with the original full-family inclusion and basis return. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledOrdinaryEq4
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace O
export GlobalCloseCompletionStopOrdinarySource (family table tract_iff_current)
end O
namespace E
export GlobalCloseCompletionC2PrimeCurrent (data old_included)
export GlobalCloseCompletionC2OrdinaryPairOutcome (HasEq4)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (P : Palette G) (anchor : E.HasEq4 (O.table G P))
include anchor in
theorem classified : Tract (O.family G P) ∨ PaperControlledHardness.Original G := by
  rcases PaperControlledOrdinary.classified G (E.data G P anchor) with tract|hard
  · exact Or.inl (tract.mono_family (E.old_included G P anchor))
  · exact Or.inr hard
include anchor in
theorem current_classified :
    TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G P)) ∨
      PaperControlledHardness.Original G := by
  rcases classified G P anchor with tract|hard
  · exact Or.inl ((O.tract_iff_current G P).mp tract)
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledOrdinaryEq4
end
