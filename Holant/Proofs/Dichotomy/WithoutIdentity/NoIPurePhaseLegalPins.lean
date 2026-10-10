import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseLegalAffine
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhasePinCompose

/-! Legal signed-recipe closure passes to actual pure pinnings of one
original row. The mixed theorem allows different retained arities in each
factor, so an anchor and a test minor use the same original closure. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseLegalPins
open Holant Holant.Tractable
open NoIPurePhaseRecipeFactor (Port word total)
open NoIPurePhaseLegalAffine (LegalAffine)
open scoped BigOperators
namespace P
export NoIPurePhasePinCompose (PurePins substitute compose word_compose total_compose)
end P
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {n m k : ℕ} {ns : Fin k→ℕ}

/-- Distinct actual pinned minors are flattened back into the same original
row before applying its legal-recipe closure. -/
theorem mixed (f : Signature AlgebraicComplex n) (legal : LegalAffine f)
    (pins : (i : Fin k)→Fin n→Bool⊕Fin (ns i)) (pure : ∀i,P.PurePins (pins i))
    (ps : (i : Fin k)→Fin (ns i)→Port m) (zero : ∀j,total ps j%4=0) :
    Affine (fun z=>∏i : Fin k,f (P.substitute (pins i) (word (ps i) z))) := by
  have hz : ∀j,total (fun i=>P.compose (pins i) (ps i)) j%4=0 := by
    rw [P.total_compose pins pure ps]
    exact zero
  have good:=legal m k (fun i=>P.compose (pins i) (ps i)) hz
  simpa only [P.word_compose] using good

theorem pin (f : Signature AlgebraicComplex n) (legal : LegalAffine f)
    (pins : Fin n→Bool⊕Fin m) (pure : P.PurePins pins) :
    LegalAffine (fun z=>f (P.substitute pins z)) := by
  intro r k ps zero
  exact mixed f legal (fun _ : Fin k=>pins) (fun _=>pure) ps zero


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseLegalPins
end
