import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedCurrent
import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedQuartic
import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedAnchor

/-! All actual shifted q4 and weighted-normalization obligations are consumed.
The positive branch is whole-current tractability; the only remaining branch
is the exact no-X ordinary obstruction, with its real ordinary and squared-CSP
programmes to original G installed. No negative backend is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedOrdinaryCurrent
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export GlobalCloseCompletionShiftedDescent (Native Descent descent)
end D
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q
namespace S
export GlobalCloseCompletionShiftedAnchor (family classified ordinarySource squareCSPSource)
end S
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
variable (native : D.Native G (palette G base R) R.final.ready.torsion)
abbrev CurrentTract := TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G (palette G base R)))
variable {o : CurrentOccurrences.Id G (palette G base R)}

abbrev sourceFamily (d : D.Descent G base R noPrior o) :=
  S.family G (palette G base R) R.final.ready.torsion native
    (Q.table G base d.four) (Q.minimum G base d.four) (Q.minimum_literal G base d.four)
    (Q.matching G base (R.preparationReceipt G base noPrior d.endpoint) d.four)

def ordinarySource (d : D.Descent G base R noPrior o) :=
  S.ordinarySource G (palette G base R) R.final.ready.torsion native
    (Q.table G base d.four) (Q.minimum G base d.four) (Q.minimum_literal G base d.four)
    (Q.matching G base (R.preparationReceipt G base noPrior d.endpoint) d.four)

def squareCSPSource (d : D.Descent G base R noPrior o) :=
  S.squareCSPSource G (palette G base R) R.final.ready.torsion native
    (Q.table G base d.four) (Q.minimum G base d.four) (Q.minimum_literal G base d.four)
    (Q.matching G base (R.preparationReceipt G base noPrior d.endpoint) d.four)

inductive Completion : Type 1 where
  | tract (criterion : CurrentTract G base R)
  | ordinary (parent : CurrentOccurrences.Id G (palette G base R))
      (higher : 4<(CurrentOccurrences.savedLeaf G (palette G base R) parent).1.1)
      (descent : D.Descent G base R noPrior parent)
      (obstruction : StableHigherCurrentOrdinaryTerminal.Obstruction (sourceFamily G base R noPrior native descent))

def complete : Completion G base R noPrior native := Classical.choice (by
  classical
  by_cases bounded : ∀o : CurrentOccurrences.Id G (palette G base R),
      (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≤4
  · exact ⟨.tract (GlobalCloseCompletionShiftedQuartic.quartic_tract G base R noPrior native bounded)⟩
  obtain ⟨o,large⟩ := not_forall.mp bounded
  have higher : 4<(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1 := by omega
  let d := D.descent G base R noPrior native o higher.le
  rcases S.classified G (palette G base R) R.final.ready.torsion native
    (Q.table G base d.four) (Q.minimum G base d.four) (Q.minimum_literal G base d.four)
    (Q.matching G base (R.preparationReceipt G base noPrior d.endpoint) d.four) with tract|negative
  · exact ⟨.tract tract⟩
  · exact ⟨.ordinary o higher d negative⟩)

def Installed (result : Completion G base R noPrior native) : Type 1 := match result with
  | .tract _ => PUnit.{2}
  | .ordinary _ _ d _ =>
      {p // p=ordinarySource G base R noPrior native d} ×
      {p // p=squareCSPSource G base R noPrior native d}

def install (result : Completion G base R noPrior native) : Installed G base R noPrior native result := match result with
  | .tract _ => PUnit.unit
  | .ordinary _ _ d _ =>
      ⟨⟨ordinarySource G base R noPrior native d,rfl⟩,⟨squareCSPSource G base R noPrior native d,rfl⟩⟩

structure Receipt : Type 1 where
  result : Completion G base R noPrior native
  resultIdentity : result=complete G base R noPrior native
  installed : Installed G base R noPrior native result

def produce : Receipt G base R noPrior native :=
  ⟨complete G base R noPrior native,rfl,install G base R noPrior native _⟩

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Type 1 := match M with
  | .shifted axis noncyclic notTwo notFour noZ reflection sameSource =>
      Receipt G base R noPrior ⟨axis,noncyclic,notTwo,notFour,noZ,reflection,sameSource⟩
  | _ => PUnit.{2}

def forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R noPrior M := by
  cases M with
  | shifted axis noncyclic notTwo notFour noZ reflection sameSource =>
      exact produce G base R noPrior ⟨axis,noncyclic,notTwo,notFour,noZ,reflection,sameSource⟩
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

def original_current_shifted_ordinary : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedOrdinaryCurrent
end
