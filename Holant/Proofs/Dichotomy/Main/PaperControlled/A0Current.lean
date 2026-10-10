import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.A0LiteralXTerminal
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0Descent
import Holant.Proofs.Dichotomy.Retained.StableCurrentBinaryClosure

/-! Actual exhausted unshifted marking continuation. Every higher current
occurrence descends through its own prepared cards to an actual q4. Sparse
q4 is fully consumed by genuine Eq4/pins/X source classification; binary-only
families are reconstructed in Product in the same Hadamard basis. A dense
normalized q4 is the sole explicit remaining unshifted mathematical case. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.A0Current
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q
namespace E
export GlobalCloseCompletionA0EqualityOriginal (CurrentTract)
end E
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
abbrev palette := R.final.source.palette
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion))
variable (nativeZ : Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.zClass∈
  ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion)
variable (sourceY : ClosureMarkedDihedralA0Resources.YResource (ClosureSourceRows.embedding G)
  (palette G base R).family R.final.ready.torsion nativeZ)

def Dense : Prop := ∃o : CurrentOccurrences.Id G (palette G base R),
  ∃four : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=4,
    ∃p : Bool,GlobalCloseCompletionA0CurrentSource.FullParity G (Q.table G base four) p

include N nativeZ sourceY in
theorem small_tract (small : ∀o : CurrentOccurrences.Id G (palette G base R),
    (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≤2) : E.CurrentTract G (palette G base R) := by
  let marking : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
      (palette G base R).family R.final.ready.torsion := .unshifted nativeZ N sourceY
  have hs := StableCurrentBinaryClosure.small_current_products G (palette G base R)
    R.final.ready.torsion marking ClosureMarkedDihedralA0.basis rfl
  have all : ∀o : CurrentOccurrences.Id G (palette G base R),
      leafPredicate G productClass ClosureMarkedDihedralA0.basis (CurrentOccurrences.savedLeaf G (palette G base R) o).1 :=
    fun o => hs.leaves o (small o)
  exact FrontierNativeClosure.relative_current_native_tractx G (palette G base R) .product
    ClosureMarkedDihedralA0.basis hs.edge
    ⟨fun o _ _ => all o,fun o _ _ => all o,fun o _ _ _ => all o,fun o _ _ _ => all o⟩

inductive Completion : Type 1 where
  | hard (proof : PaperControlledHardness.Original G)
  | tract (criterion : E.CurrentTract G (palette G base R))
  | dense (full : Dense G base R)

def complete : Completion G base R := Classical.choice (by
  classical
  by_cases small : ∀o : CurrentOccurrences.Id G (palette G base R),
      (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≤2
  · exact ⟨.tract (small_tract G base R N nativeZ sourceY small)⟩
  · obtain ⟨o,ho⟩ := not_forall.mp small
    have nonbinary : 3≤(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1 := by omega
    have even := R.final.ready.noOdd _ (CurrentOccurrences.savedLeaf_retained G (palette G base R) o)
      (CurrentOccurrences.savedLeaf_prime G (palette G base R) o) nonbinary
    have proper : 4≤(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1 := by
      rcases even with ⟨k,hk⟩
      omega
    obtain ⟨endpt,_path,four⟩ := GlobalCloseCompletionA0Descent.quaternary_path_exists
      G base R noPrior N o proper
    let q := Q.table G base four
    let core := Q.minimum G base four
    have literal : core.signature=⟨4,q⟩ := Q.minimum_literal G base four
    have stable := Q.matching G base (R.preparationReceipt G base noPrior endpt) four
    rcases PaperControlled.A0LiteralXTerminal.dense_or_classified G (palette G base R)
      R.final.ready.torsion N q core literal stable with dense|tract|hard
    · exact ⟨.dense ⟨endpt,four,dense⟩⟩
    · exact ⟨.tract tract⟩
    · exact ⟨.hard hard⟩)

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Type 1 := match M with
  | .unshifted _ _ _ => Completion G base R
  | _ => PUnit.{2}

def forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R M := by
  cases M with
  | unshifted z native source => exact complete G base R noPrior native z source
  | smallTwo => exact PUnit.unit
  | smallFour => exact PUnit.unit
  | cyclic => exact PUnit.unit
  | monomial => exact PUnit.unit
  | bilinear => exact PUnit.unit
  | shifted => exact PUnit.unit
  | platonic => exact PUnit.unit

def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 := match result with
  | .initialStop .. => PUnit.{2}
  | .prepared _ _ (.inl _) => PUnit.{2}
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := match result with
  | .initialStop .. => PUnit.unit
  | .prepared _ _ (.inl _) => PUnit.unit
  | .prepared _ _ (.inr exhausted) =>
      forMarking G base exhausted rfl (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

def original_current_unshifted_resolved : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.A0Current
end
