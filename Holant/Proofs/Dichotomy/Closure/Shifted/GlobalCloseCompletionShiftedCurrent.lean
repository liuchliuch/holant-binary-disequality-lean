import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedDescent
import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedPrepared
import Holant.Proofs.Dichotomy.Retained.StableCurrentBinaryClosure
import Holant.Proofs.Closure.GeneratedGroupQ4Consumers

/-! Actual exhausted shifted-marking continuation. Binary-only current
families close in Product at the same selected basis. Every other branch
constructs an addressed descent to a real prepared q4 and installs its weighted
source graph and original-G open return. Ordinary normalization is not assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace D
export GlobalCloseCompletionShiftedDescent (Native Descent descent)
end D
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q
namespace H
export GlobalCloseCompletionShiftedQuaternary (Receipt produce)
end H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
abbrev palette := R.final.source.palette
variable (native : D.Native G (palette G base R) R.final.ready.torsion)
abbrev CurrentTract := TractX (familyAction sourceKBasis
  (CurrentFrontierClosure.currentFamily G (palette G base R)))

include native in
theorem small_tract (small : ∀o : CurrentOccurrences.Id G (palette G base R),
    (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≤2) : CurrentTract G base R := by
  have hs := StableCurrentBinaryClosure.small_current_products G (palette G base R)
    R.final.ready.torsion (native.marking G) native.reflection.basis rfl
  have all : ∀o : CurrentOccurrences.Id G (palette G base R),
      leafPredicate G productClass native.reflection.basis
        (CurrentOccurrences.savedLeaf G (palette G base R) o).1 :=
    fun o => hs.leaves o (small o)
  exact FrontierNativeClosure.relative_current_native_tractx G (palette G base R)
    .product native.reflection.basis hs.edge
    ⟨fun o _ _ => all o,fun o _ _ => all o,fun o _ _ _ => all o,fun o _ _ _ => all o⟩

inductive Completion : Type 1 where
  | tract (criterion : CurrentTract G base R)
  | quaternary (parent : CurrentOccurrences.Id G (palette G base R))
      (proper : 4≤(CurrentOccurrences.savedLeaf G (palette G base R) parent).1.1)
      (descent : D.Descent G base R noPrior parent)
      (physical : H.Receipt G (palette G base R) R.final.ready.torsion native
        (Q.table G base descent.four) (Q.minimum G base descent.four)
        (Q.minimum_literal G base descent.four)
        (Q.matching G base (R.preparationReceipt G base noPrior descent.endpoint) descent.four))

def complete : Completion G base R noPrior native := Classical.choice (by
  classical
  by_cases small : ∀o : CurrentOccurrences.Id G (palette G base R),
      (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≤2
  · exact ⟨.tract (small_tract G base R native small)⟩
  obtain ⟨o,large⟩ := not_forall.mp small
  have three : 3≤(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1 := by omega
  have even := R.final.ready.noOdd _ (CurrentOccurrences.savedLeaf_retained G (palette G base R) o)
    (CurrentOccurrences.savedLeaf_prime G (palette G base R) o) three
  have proper : 4≤(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1 := by
    obtain ⟨k,hk⟩ := even
    omega
  let d := D.descent G base R noPrior native o proper
  exact ⟨.quaternary o proper d
    (GlobalCloseCompletionShiftedPrepared.fromCurrent G base
      (R.preparationReceipt G base noPrior d.endpoint) d.four native)⟩)

/-- Only the actual shifted branch is handled; its complete seven-field
marking determines the same retained reflection in every installed graph. -/
def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Type 1 := match M with
  | .shifted axis noncyclic notTwo notFour noZ reflection sameSource =>
      Completion G base R noPrior ⟨axis,noncyclic,notTwo,notFour,noZ,reflection,sameSource⟩
  | _ => PUnit.{2}

def forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R noPrior M := by
  cases M with
  | shifted axis noncyclic notTwo notFour noZ reflection sameSource =>
      exact complete G base R noPrior ⟨axis,noncyclic,notTwo,notFour,noZ,reflection,sameSource⟩
  | smallTwo => exact PUnit.unit
  | smallFour => exact PUnit.unit
  | cyclic => exact PUnit.unit
  | monomial => exact PUnit.unit
  | bilinear => exact PUnit.unit
  | unshifted => exact PUnit.unit
  | platonic => exact PUnit.unit

def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 := match result with
  | .initialStop .. => PUnit.{2}
  | .prepared _ _ (.inl _) => PUnit.{2}
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted rfl (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := match result with
  | .initialStop .. => PUnit.unit
  | .prepared _ _ (.inl _) => PUnit.unit
  | .prepared _ _ (.inr exhausted) =>
      forMarking G base exhausted rfl (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

def original_current_shifted : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedCurrent
end
