import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4FullSource
import Holant.Proofs.Dichotomy.Closure.Affine.GlobalCloseCompletionAffineAncestorEq4
import Holant.Proofs.Dichotomy.Closure.Higher.GlobalCloseCompletionHigherBases
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentNativeM

/-! A genuine higher native-M Product branch has a prepared q4 descendant.
That actual prime row produces scalar Eq4, so the entire current family gets
ordinary two-pin and even-CSP access. No Product ancestor theorem is needed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4Current
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
open GlobalCloseCompletionMixedCurrent
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion))
variable (C : EOClass)
variable (basis : IsCommonKBasis (GlobalCloseCompletionNativeMContinuation.classFamily C) (family G base R) InvertibleKernel.identity)
variable (noDense : ¬Dense G base R)

include noPrior N C basis noDense in
/-- A prepared sparse q4 Product occurrence has the actual Eq4 graph output. -/
theorem from_quaternary (o : CurrentOccurrences.Id G (palette G base R))
    (four : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=4) :
    Nonempty (GlobalCloseCompletionEq4Graph.Output G (palette G base R)) := by
  let q := Q.table G base four
  let core := Q.minimum G base four
  have literal : core.signature=⟨4,q⟩ := Q.minimum_literal G base four
  have matching := Q.matching G base (R.preparationReceipt G base noPrior o) four
  have sparse : ¬∃p : Bool,StableCurrentEvenEOTransport.FullParity G q p := by
    rintro ⟨p,hp⟩
    exact noDense ⟨o,four,p,hp⟩
  obtain ⟨d⟩ := (StableCurrentEvenEOTransport.sparse_or_full G (palette G base R)
    R.final.ready.torsion N q core literal matching).resolve_left sparse
  have member := GlobalCloseCompletionHigherBases.quaternary G base R C basis noDense o four
  have hq : (⟨4,q⟩ : AnySignature (OI.K G))=(CurrentOccurrences.savedLeaf G (palette G base R) o).1 :=
    FrontierQ4.tableFour_exact _ four
  rw [←hq] at member
  have hC : C.Holds (StableCurrentEvenEOTransport.embedded G q) := by
    cases C with
    | affine =>
        change Affine (embed G ⟨4,q⟩).2
        change Affine (InvertibleKernel.identity.symm.action (embed G ⟨4,q⟩).2) at member
        simpa only [InvertibleKernel.identity_symm,InvertibleKernel.identity_action] using member
    | product =>
        change Product (embed G ⟨4,q⟩).2
        change Product (InvertibleKernel.identity.symm.action (embed G ⟨4,q⟩).2) at member
        simpa only [InvertibleKernel.identity_symm,InvertibleKernel.identity_action] using member
  cases C with
  | affine =>
      exact GlobalCloseCompletionAffineAncestorEq4.produce G (palette G base R)
        R.final.ready.torsion N q core literal matching d hC
  | product => exact GlobalCloseCompletionSparseEq4Product.produce G (palette G base R) q core literal d hC


include noPrior N C basis noDense in
/-- Exact finite descent replaces the formerly unresolved Product ancestor
with one real Eq4 graph over the same final original-field palette. -/
theorem from_higher (o : CurrentOccurrences.Id G (palette G base R))
    (higher : 4<(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1) :
    Nonempty (GlobalCloseCompletionEq4Graph.Output G (palette G base R)) := by
  obtain ⟨q,_path,four⟩ := StableHigherCurrentNativeM.quaternary_path_exists
    G base R noPrior N o higher.le
  exact from_quaternary G base R noPrior N C basis noDense q four

variable (o : CurrentOccurrences.Id G (palette G base R))
variable (higher : 4<(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1)

def output : GlobalCloseCompletionEq4Graph.Output G (palette G base R) :=
  Classical.choice (from_higher G base R noPrior N C basis noDense o higher)

def ordinarySource := GlobalCloseCompletionEq4FullSource.ordinarySource G (palette G base R)
  (output G base R noPrior N C basis noDense o higher)
def evenCSPSource := GlobalCloseCompletionEq4FullSource.evenCSPSource G (palette G base R)
  (output G base R noPrior N C basis noDense o higher)
def squareCSPSource := GlobalCloseCompletionEq4FullSource.squareCSPSource G (palette G base R)
  (output G base R noPrior N C basis noDense o higher)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4Current
end
