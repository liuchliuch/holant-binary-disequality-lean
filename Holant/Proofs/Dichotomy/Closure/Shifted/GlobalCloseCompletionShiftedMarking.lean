import Holant.Proofs.Closure.ClosureMarkedActualReceipts
import Holant.Proofs.Closure.ClosureSourceRows

/-! Exact actual shifted-marking data, retaining the original reflection. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedMarking
open Holant Holant.Tractable
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- Exactly the seven fields carried by the actual shifted marking. -/
structure Native (P : Palette G) (torsion : ResidualTorsion P.family) : Type 1 where
  axis : ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion ≤
    Subgroup.centralizer ({Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.xClass} : Set (PGL2 ℂ))
  noncyclic : ¬IsCyclic (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion)
  notTwo : Nat.card (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion)≠2
  notFour : Nat.card (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion)≠4
  noZ : Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.zClass ∉
    ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion
  reflection : ClosureMarkedShiftReflection.Reflection (ClosureSourceRows.embedding G) P.family torsion
  sameSource : reflection=ClosureMarkedShiftReflection.select (ClosureSourceRows.embedding G)
    P.family torsion axis noncyclic

def Native.marking {P : Palette G} {torsion : ResidualTorsion P.family}
    (N : Native G P torsion) :
    ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G) P.family torsion :=
  .shifted N.axis N.noncyclic N.notTwo N.notFour N.noZ N.reflection N.sameSource

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedMarking
end
