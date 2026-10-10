import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseSource
import Holant.Proofs.Closure.GeneratedGroupQ4Consumers
import Holant.Proofs.Closure.GeneratedGroupWorklistAccess
import Holant.Proofs.Closure.ClosureMarkedActualReceipts

/-! Complete sparse-quaternary current occurrence selection and physical
simultaneous closure. Every sparse q4 occurrence is selected from the same
exhausted final ledger, with its own preparation event. One A/P identity basis
holds for the entire selected original family, or original G is counting-hard.
Dense rows and higher ancestors keep their separate mathematical obligations. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open StableCurrentEvenEOTransport StableCurrentEvenLocalOutcome
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A)

def Sparse (o : CurrentOccurrences.Id G R.final.source.palette) : Prop :=
  ∃four : (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1=4,
    ¬∃p : Bool,FullParity G (Q.table G base four) p

abbrev Index := {o : CurrentOccurrences.Id G R.final.source.palette // Sparse G base R o}
local instance : Fintype (Index G base R) := Fintype.ofFinite _
abbrev count := Fintype.card (Index G base R)
def occurrence (i : Fin (count G base R)) : Index G base R := (Fintype.equivFin _).symm i

theorem four (i : Fin (count G base R)) :
    (CurrentOccurrences.savedLeaf G R.final.source.palette (occurrence G base R i).val).1.1=4 :=
  (occurrence G base R i).property.choose

abbrev table (i : Fin (count G base R)) : Signature (OI.K G) 4 := Q.table G base (four G base R i)
abbrev core (i : Fin (count G base R)) := Q.minimum G base (four G base R i)
theorem literal (i : Fin (count G base R)) : (core G base R i).signature=⟨4,table G base R i⟩ :=
  Q.minimum_literal G base (four G base R i)

theorem sparse (i : Fin (count G base R)) : ¬∃p : Bool,FullParity G (table G base R i) p :=
  (occurrence G base R i).property.choose_spec

theorem complete (o : CurrentOccurrences.Id G R.final.source.palette) (ho : Sparse G base R o) :
    ∃i : Fin (count G base R),(occurrence G base R i).val=o := by
  refine ⟨Fintype.equivFin _ ⟨o,ho⟩,?_⟩
  exact congrArg Subtype.val ((Fintype.equivFin _).symm_apply_apply ⟨o,ho⟩)

variable (noPrior : A.source.done=∅)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    R.final.source.palette.family R.final.ready.torsion))

include noPrior in
theorem matching (i : Fin (count G base R)) :
    ∀f∈rawDeck R.final.source.palette.family R.final.ready.torsion (table G base R i),
      Holant.Certificates.MatchingContractionClosure.MatchingOrZero
        (Holant.Projective.BoundedTorsion.actualTransfers R.final.source.palette.family) f :=
  Q.matching G base (R.preparationReceipt G base noPrior (occurrence G base R i).val) (four G base R i)

def output (i : Fin (count G base R)) :
    SparseOutput G R.final.source.palette (table G base R i) (core G base R i) (literal G base R i) :=
  Classical.choice ((sparse_or_full G R.final.source.palette R.final.ready.torsion N
    (table G base R i) (core G base R i) (literal G base R i) (matching G base R noPrior i)).resolve_left
      (sparse G base R i))

def family : SignatureFamily AlgebraicComplex :=
  GlobalCloseCompletionSparseFamily.originalFamily G (table G base R)

def Outcome : Prop :=
  (IsCommonKBasis affineClass (family G base R) InvertibleKernel.identity ∨
    IsCommonKBasis productClass (family G base R) InvertibleKernel.identity) ∨ OriginalHard G

include noPrior N in
/-- Preparation, all physical EO graphs and the joint source are constructed
from the actual complete current occurrence ledger. -/
theorem outcome : Outcome G base R :=
  GlobalCloseCompletionSparseSource.simultaneous_basis_or_hard G R.final.source.palette
    R.final.ready.torsion N (table G base R) (core G base R) (literal G base R)
    (matching G base R noPrior) (output G base R noPrior N)

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    R.final.source.palette.family R.final.ready.torsion) : Prop :=
  match M with
  | .monomial _ => Outcome G base R
  | _ => True

include noPrior in
theorem forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    R.final.source.palette.family R.final.ready.torsion) : ForMarking G base R M := by
  cases M with
  | monomial N => exact outcome G base R noPrior N
  | smallTwo => trivial
  | smallFour => trivial
  | cyclic => trivial
  | bilinear => trivial
  | unshifted => trivial
  | shifted => trivial
  | platonic => trivial

def ForResult (result : GeneratedGroupWorklist.Result G base) : Prop :=
  match result with
  | .initialStop .. => True
  | .prepared _ _ (.inl _) => True
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

theorem forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := by
  cases result with
  | initialStop => trivial
  | prepared ready recomputed completion =>
      cases completion with
      | inl => trivial
      | inr exhausted => exact forMarking G base exhausted rfl _

theorem original_current_sparse_family : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseCurrent
end
