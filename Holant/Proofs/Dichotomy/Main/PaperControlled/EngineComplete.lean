import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineTransitions
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineStructuralResolution
import Holant.Proofs.Dichotomy.Main.PaperControlledStop
import Holant.Proofs.Dichotomy.Retained.StablePaletteTractability

/-! Unconditional supplied-I whole-engine closure. Every initial/prepared
stop and every exhausted marking is consumed by its proved producer. The
positive branch gives one criterion for the entire current family, and the
negative branch targets the unchanged original input. This module is the
supplied-I engine endpoint, not the distinct no-I quaternary theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.EngineComplete
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace T
export PaperControlled.EngineTransitions (CurrentTract Hard current_mono)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G

theorem classified (P : Palette G) : T.CurrentTract G P ∨ T.Hard G := by
  cases PaperControlled.EngineStructuralResolution.complete G P with
  | tract criterion=>exact Or.inl criterion
  | hard proof=>exact Or.inr proof
  | stopped Q old stop=>
    rcases PaperControlledStop.classified G Q stop with tract|hard
    · exact Or.inl (T.current_mono G P Q old tract)
    · exact Or.inr hard

theorem original_current_classified :
    T.CurrentTract G (Initial.palette G) ∨ T.Hard G :=classified G (Initial.palette G)

theorem inFP_or_countingHard :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) ∨ T.Hard G := by
  rcases original_current_classified G with tract|hard
  · exact Or.inl (StablePaletteTractability.original_inFP G (Initial.palette G) tract)
  · exact Or.inr hard


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.EngineComplete
end
