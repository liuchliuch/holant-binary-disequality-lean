import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralEq4
import Holant.Proofs.Dichotomy.Main.PaperControlled.OctahedralDenseEndpoint
import Holant.Proofs.Dichotomy.Main.PaperControlled.Eq4Universal

/-! Actual-current marked O at four ports, with both complete alternatives.
Every marked form now supplies a whole-current common basis or counting
hardness for the unchanged original signature family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.OctahedralQ4
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedReversalOvergroup.Ambient
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family)
abbrev CurrentTract := GlobalCloseCompletionEq4Classification.CurrentTract G P
abbrev Hard := PaperControlledHardness.Original G

theorem endpoint_classified (output : GlobalCloseCompletionOctahedralEndpointCurrent.Output G P tau) :
    CurrentTract G P ∨ Hard G := by
  by_cases dd : output.form=0
  · obtain ⟨eq4⟩ := GlobalCloseCompletionOctahedralEq4.source G P tau output dd
    exact PaperControlled.Eq4Universal.classified G P eq4
  · exact PaperControlled.OctahedralDenseEndpoint.classified G P tau output dd

theorem current_classified (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
    (same : core.signature=⟨4,q⟩)
    (stable : ∀f∈rawDeck P.family tau q,MatchingOrZero (actualTransfers P.family) f)
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G) P.family tau)
      (.platonic .octahedral)) : CurrentTract G P ∨ Hard G := by
  obtain ⟨output⟩ := GlobalCloseCompletionOctahedralEndpointCurrent.produce G P tau q core same stable semantic
  exact endpoint_classified G P tau output

variable (base : Palette G)
variable {S U : GeneratedGroupWorklist.Active G base}
variable {trace : GeneratedGroupWorklist.Trace G base S U}
variable {o : CurrentOccurrences.Id G U.source.palette}
variable (receipt : GeneratedGroupWorklist.PreparationReceipt G base trace o)
variable (four : (CurrentOccurrences.savedLeaf G U.source.palette o).1.1=4)

include receipt four in
theorem prepared_classified
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
      U.source.palette.family U.ready.torsion) (.platonic .octahedral)) :
    CurrentTract G U.source.palette ∨ Hard G := by
  obtain ⟨output⟩ := GlobalCloseCompletionOctahedralEndpointCurrent.prepared G base receipt four semantic
  exact endpoint_classified G U.source.palette U.ready.torsion output


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.OctahedralQ4
end
