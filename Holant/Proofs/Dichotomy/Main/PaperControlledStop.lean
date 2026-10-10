import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopStructuralSource
import Holant.Proofs.Dichotomy.Main.PaperControlledUnary

/-! Whole-family structural-stop classification retaining the actual
controlled original-G hardness programme through every source branch. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledStop
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (P : Palette G)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false

theorem classified (stop : OccurrenceWorklist.Stop G P) :
    TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G P)) ∨
      PaperControlledHardness.Original G := by
  cases GlobalCloseCompletionStopStructuralSource.complete G P stop with
  | tract criterion=>exact Or.inl criterion
  | source data=>exact Or.inr (PaperControlledUnary.countingHard G data)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledStop
end
