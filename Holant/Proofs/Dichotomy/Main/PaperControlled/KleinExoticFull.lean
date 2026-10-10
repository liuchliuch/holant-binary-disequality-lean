import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinEq4Source
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinExoticSix
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinExoticResolved

/-! The actual exotic small-four stable exit closes at every even arity.
Higher six/eight-port matching certificates force a proper original-field
split, leaving the actual minimum quaternary to the ordinary Eq4 terminal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinExoticFull
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
variable (exotic : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.exotic)

include cardinal noncyclic exotic in
theorem classified {m : ℕ} (f : Signature (OI.K G) (m+2)) (proper : 2≤m)
    (even : Even (m+2)) (core : MinimumCore P.family) (literal : core.signature=⟨m+2,f⟩)
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    PaperControlled.KleinEq4Source.CurrentTract G P ∨ PaperControlled.KleinEq4Source.Hard G := by
  have prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)) := by simpa only [literal] using core.prime
  have h := GlobalCloseCompletionKleinExoticSix.stable_prime_residual_eq_two
    G P torsion cardinal noncyclic exotic f proper even prime stable
  subst m
  exact PaperControlled.KleinExoticResolved.classified
    G P torsion cardinal noncyclic exotic f core literal stable

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinExoticFull
end
