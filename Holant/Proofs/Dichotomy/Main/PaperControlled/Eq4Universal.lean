import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinary
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Classification
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.Eq4Universal
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (P : Palette G) (o : GlobalCloseCompletionEq4Graph.Output G P)
include o in
theorem classified : GlobalCloseCompletionEq4Classification.CurrentTract G P ∨
    PaperControlledHardness.Original G := by
  rcases PaperControlledOrdinary.literalX_classified G (GenericLiteralXSource.ofEq4 G P o) with tract|hard
  · exact Or.inl (GlobalCloseCompletionEq4Classification.tractX_of_tract G P o tract)
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.Eq4Universal
end
