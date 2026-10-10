import Holant.Proofs.Closure.ClosureCyclicCurrentGrowth
import Holant.Proofs.Closure.OccurrenceWorklist

/-! Closed inspection after genuine doubled-factor installation. It returns an
actual retained structural exit with source programmes, or recomputed residual
torsion and a PROVED strict actual complete-group growth at that same palette.
No successful readiness, future group or continuation compiler is supplied. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (τ : ResidualTorsion P.family)
variable (N : C.NativeCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))
variable (d : CyclicBoundary.NonsquareExit.DoubledOutside
  (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) N.m)

inductive DoubledContinuation : Type 1
  | stopped (stop : OccurrenceWorklist.Stop G (installedPalette G P d))
      (physical : RetainedFinalAccess.Access G (installedPalette G P d) (OccurrenceWorklist.Stop.structural G stop))
  | growth (ready : OccurrenceWorklist.Ready G (installedPalette G P d))
      (strict : completeGroup P.family τ < completeGroup (installedPalette G P d).family ready.torsion)

def doubledContinuation : DoubledContinuation G P τ N d := by
  cases OccurrenceWorklist.inspect G (installedPalette G P d) with
  | inl stop =>
    exact .stopped stop
      (RetainedFinalAccess.forStructuralExit G (installedPalette G P d) (OccurrenceWorklist.Stop.structural G stop))
  | inr ready => exact .growth ready (installed_group_growth G P τ N d ready.torsion)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
