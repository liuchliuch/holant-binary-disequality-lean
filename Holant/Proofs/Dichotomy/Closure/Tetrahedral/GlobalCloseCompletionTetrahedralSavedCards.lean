import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralCurrent
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentCoverage

/-! Every final prepared T q4 occurrence is impossible. The original saved
factor tree of each six-port raw card therefore consists entirely of actual
binary leaves at the final group, including all newly installed occurrences. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralCurrentLeaves
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient
open StableHigherCurrentCoverage
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
abbrev palette := R.final.source.palette
variable (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
  (palette G base R).family R.final.ready.torsion) (.platonic .tetrahedral))

include noPrior semantic in
theorem no_quaternary (o : CurrentOccurrences.Id G (palette G base R))
    (four : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=4) : False :=
  GlobalCloseCompletionTetrahedralCurrent.prepared_semantic_tetrahedral_impossible
    G base (R.preparationReceipt G base noPrior o) four semantic

include noPrior semantic in
theorem six_matching (o : CurrentOccurrences.Id G (palette G base R))
    (proper : 4≤(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1)
    (six : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=6) :
    ∀q∈rawDeck (palette G base R).family R.final.ready.torsion
      (input G base (R.preparationReceipt G base noPrior o) proper).signature,
      MatchingOrZero (actualTransfers (palette G base R).family) q := by
  let r := R.preparationReceipt G base noPrior o
  change (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1=6 at six
  intro q hq
  rcases hq with hz|⟨k,rfl⟩
  · exact Or.inl hz
  by_cases hz : current G base r proper k=0
  · exact Or.inl hz
  apply matching_of_binary_leaves G base r proper k hz
  intro p
  rcases cardLeaf_cases G base r proper k hz p with two|higher
  · exact two
  · have bound := cardLeaf_arity_le G base r proper k hz p
    have size := congrArg Sigma.fst (r.selectedSignatureFinal G base proper)
    change (input G base r proper).m+2=_ at size
    have four : (CurrentOccurrences.savedLeaf G R.final.source.palette
        (cardLeaf G base r proper k hz p)).1.1=4 := by omega
    exact (no_quaternary G base R noPrior semantic _ four).elim


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralCurrentLeaves
end
