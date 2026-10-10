import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedQuaternary
import Holant.Proofs.Closure.GeneratedGroupQ4Consumers

/-! Install the weighted shifted source at each actual prepared current q4.
Preparation supplies the matching deck; no independent local-stability input
or equal-valued replacement occurrence is accepted by the root producer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedPrepared
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace N
export GlobalCloseCompletionShiftedMarking (Native)
end N
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
variable {S T : GeneratedGroupWorklist.Active G base}
variable {h : GeneratedGroupWorklist.Trace G base S T}
variable {o : CurrentOccurrences.Id G T.source.palette}
variable (r : GeneratedGroupWorklist.PreparationReceipt G base h o)
variable (four : (CurrentOccurrences.savedLeaf G T.source.palette o).1.1=4)
variable (native : N.Native G T.source.palette T.ready.torsion)

def fromCurrent : H.Receipt G T.source.palette T.ready.torsion native
    (Q.table G base four) (Q.minimum G base four) (Q.minimum_literal G base four)
    (Q.matching G base r four) :=
  H.produce G T.source.palette T.ready.torsion native
    (Q.table G base four) (Q.minimum G base four) (Q.minimum_literal G base four)
    (Q.matching G base r four)

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    T.source.palette.family T.ready.torsion) : Type 1 := match M with
  | .shifted axis noncyclic notTwo notFour noZ reflection sameSource =>
      H.Receipt G T.source.palette T.ready.torsion
        ⟨axis,noncyclic,notTwo,notFour,noZ,reflection,sameSource⟩
        (Q.table G base four) (Q.minimum G base four) (Q.minimum_literal G base four)
        (Q.matching G base r four)
  | _ => PUnit.{2}

def forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    T.source.palette.family T.ready.torsion) : ForMarking G base r four M := by
  cases M with
  | shifted axis noncyclic notTwo notFour noZ reflection sameSource =>
      exact fromCurrent G base r four ⟨axis,noncyclic,notTwo,notFour,noZ,reflection,sameSource⟩
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
      ∀ (o : CurrentOccurrences.Id G exhausted.final.source.palette)
        (four : (CurrentOccurrences.savedLeaf G exhausted.final.source.palette o).1.1=4),
        ForMarking G base (exhausted.preparationReceipt G base rfl o) four
          (ClosureMarkedActualReceipts.produce G exhausted.final.source.palette
            exhausted.final.ready.torsion).physical.marking

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := match result with
  | .initialStop .. => PUnit.unit
  | .prepared _ _ (.inl _) => PUnit.unit
  | .prepared _ _ (.inr exhausted) =>
      fun o four => forMarking G base (exhausted.preparationReceipt G base rfl o) four _

def original_current_shifted_q4 : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedPrepared
end
