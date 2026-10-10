import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinaryData
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryComplete

/-! Controlled whole-family ordinary classification on the unchanged
original-G oracle. The universal terminal derives its actual resources
internally, retaining the complete counted-verifier source programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledOrdinary
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (src : GenericOrdinarySource.Data G)

theorem classified : Tract (GenericOrdinarySource.family G src) ∨ PaperControlledHardness.Original G :=
  NoIOrdinaryRaw.NoIOrdinaryComplete.classified (PaperControlledHardness.originalTarget G)
    (PaperControlledOrdinaryData.data G src)

theorem countingHard (negative : ¬Tract (GenericOrdinarySource.family G src)) :
    PaperControlledHardness.Original G := (classified G src).resolve_left negative

theorem of_obstruction (negative : StableHigherCurrentOrdinaryTerminal.Obstruction
    (preprocess (GenericOrdinarySource.family G src))) : PaperControlledHardness.Original G :=
  countingHard G src ((GenericOrdinarySource.rejected_iff G src).mpr negative)

theorem literalX_classified (source : GenericLiteralXSource.Data G) :
    Tract (GenericLiteralXSource.family G source) ∨ PaperControlledHardness.Original G :=
  classified G (GenericOrdinarySource.ofLiteralX G source)

theorem literalX_countingHard (source : GenericLiteralXSource.Data G)
    (negative : StableHigherCurrentOrdinaryTerminal.Obstruction
      (preprocess (GenericLiteralXSource.family G source))) : PaperControlledHardness.Original G :=
  of_obstruction G (GenericOrdinarySource.ofLiteralX G source) negative


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledOrdinary
end
