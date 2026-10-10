import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedEqualityMask
import Holant.Proofs.Dichotomy.Retained.StableCurrentBinaryClosure
import Holant.Proofs.Closure.GeneratedGroupQ4Consumers
import Holant.Proofs.Dichotomy.Retained.StablePaletteTractability

/-! Whole-current Product closure when every actual saved shifted prime has
arity at most four. Each q4 uses its own prepared full deck; all leaves and
the native edge share the exact same selected shifted basis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedQuartic
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q
namespace E
export GlobalCloseCompletionShiftedEqualityMask (sector_product)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
abbrev palette := R.final.source.palette
variable (native : GlobalCloseCompletionShiftedMarking.Native G (palette G base R) R.final.ready.torsion)
abbrev CurrentTract := TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G (palette G base R)))

include noPrior native in
theorem four_product (o : CurrentOccurrences.Id G (palette G base R))
    (four : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=4) :
    leafPredicate G productClass native.reflection.basis (CurrentOccurrences.savedLeaf G (palette G base R) o).1 := by
  have member : leafPredicate G productClass native.reflection.basis ⟨4,Q.table G base four⟩ :=
    E.sector_product G (palette G base R) R.final.ready.torsion native
      (Q.table G base four) (Q.minimum G base four) (Q.minimum_literal G base four)
      (Q.matching G base (R.preparationReceipt G base noPrior o) four)
  have literal : (⟨4,Q.table G base four⟩ : AnySignature (OI.K G))=
      (CurrentOccurrences.savedLeaf G (palette G base R) o).1 :=
    FrontierQ4.tableFour_exact (CurrentOccurrences.savedLeaf G (palette G base R) o).1 four
  exact (congrArg (leafPredicate G productClass native.reflection.basis) literal).mp member

include noPrior native in
theorem quartic_tract (bounded : ∀o : CurrentOccurrences.Id G (palette G base R),
    (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≤4) : CurrentTract G base R := by
  have hs := StableCurrentBinaryClosure.small_current_products G (palette G base R)
    R.final.ready.torsion (native.marking G) native.reflection.basis rfl
  have all : ∀o : CurrentOccurrences.Id G (palette G base R),
      leafPredicate G productClass native.reflection.basis
        (CurrentOccurrences.savedLeaf G (palette G base R) o).1 := by
    intro o
    by_cases small : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≤2
    · exact hs.leaves o small
    · have three : 3≤(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1 := by omega
      have even := R.final.ready.noOdd _ (CurrentOccurrences.savedLeaf_retained G (palette G base R) o)
        (CurrentOccurrences.savedLeaf_prime G (palette G base R) o) three
      have four : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=4 := by
        have bound := bounded o
        obtain ⟨k,hk⟩ := even
        omega
      exact four_product G base R noPrior native o four
  exact FrontierNativeClosure.relative_current_native_tractx G (palette G base R)
    .product native.reflection.basis hs.edge
    ⟨fun o _ _ => all o,fun o _ _ => all o,fun o _ _ _ => all o,fun o _ _ _ => all o⟩

include noPrior native in
theorem quartic_inFP (bounded : ∀o : CurrentOccurrences.Id G (palette G base R),
    (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≤4) :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) :=
  StablePaletteTractability.original_inFP G (palette G base R) (quartic_tract G base R noPrior native bounded)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedQuartic
end
