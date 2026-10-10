import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinEq4Source
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinStandardDense
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinExoticResolved

/-! Complete actual stable minimum-quaternary small-four dispatch. Standard
and exotic are selected from the genuine current complete group; neither a
successful chart nor an assumed row terminal is supplied by the caller. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinQuaternaryResolved
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))

include cardinal noncyclic in
theorem classified (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (literal : core.signature=⟨4,q⟩)
    (stable : ∀g∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) g) :
    PaperControlled.KleinEq4Source.CurrentTract G P ∨ PaperControlled.KleinEq4Source.Hard G := by
  cases kind : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic with
  | standard =>
      exact PaperControlled.KleinStandardDense.classified G P torsion q core literal
        cardinal noncyclic kind stable
  | exotic =>
      exact PaperControlled.KleinExoticResolved.classified G P torsion cardinal noncyclic kind
        q core literal stable

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinQuaternaryResolved
end
