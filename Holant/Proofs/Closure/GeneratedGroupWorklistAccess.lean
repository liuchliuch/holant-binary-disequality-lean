import Holant.Proofs.Closure.GeneratedGroupWorklistRetention
import Holant.Proofs.Closure.GeneratedDeckTransportAccess

/-! Real FINAL-Q+raw-card original-G programmes extracted from an actual
current-group preparation receipt. The copied old-batch label map is the actual
suffix map. All current raw keys, actual zero keys and the standalone sentinel
are handled without choosing a new factor tree or supplying a compiler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupWorklist
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)

/-- This view is extracted by actual constructor inspection of the selected
physical preparation event, not by a same-arity minimum or a new factorization. -/
structure HigherEventData {S T : Source G base} (e : GeneratedOccurrenceWorklist.Transition G base S T) : Type 1 where
  pending : e.selected G base ∈ S.todo
  ready : OccurrenceWorklist.Ready G S.palette
  recomputed : OccurrenceWorklist.inspect G S.palette = .inr ready
  input : GeneratedOccurrenceWorklist.Input G S.palette (e.selected G base)
  eventIdentity : HEq e (GeneratedOccurrenceWorklist.Transition.higher S (e.selected G base) pending ready recomputed input)
  paletteIdentity : OccurrenceBatch.palette G S.palette ready.torsion input.signature input.retained input.proper = T.palette

def higherEventData {S T : Source G base} (e : GeneratedOccurrenceWorklist.Transition G base S T)
    (hfour : 4 ≤ GeneratedOccurrenceWorklist.weight G S.palette (e.selected G base)) : HigherEventData G base e := by
  cases e with
  | binary o pending ready recomputed htwo =>
    change 4 ≤ GeneratedOccurrenceWorklist.weight G S.palette o at hfour
    omega
  | higher o pending ready recomputed input => exact ⟨pending,ready,recomputed,input,HEq.rfl,rfl⟩

variable {S T : Active G base} {h : Trace G base S T} {q : CurrentOccurrences.Id G T.source.palette}
variable (r : PreparationReceipt G base h q)
variable (hfour : 4 ≤ (CurrentOccurrences.savedLeaf G T.source.palette q).1.1)

def PreparationReceipt.higherData : HigherEventData G base (r.event.preparation G base) :=
  higherEventData G base (r.event.preparation G base)
    (hfour.trans_eq (congrArg (fun u : TreeOccurrence (OI.K G) => u.1.1) r.leafExact))

abbrev PreparationReceipt.oldBatch :=
  OccurrenceBatch.palette G r.before.source.palette (r.higherData G base hfour).ready.torsion
    (r.higherData G base hfour).input.signature (r.higherData G base hfour).input.retained
    (r.higherData G base hfour).input.proper

theorem PreparationReceipt.oldBatchAfter : r.oldBatch G base hfour = r.after.source.palette :=
  (r.higherData G base hfour).paletteIdentity.trans (r.event.raw_paletteIdentity G base)

theorem PreparationReceipt.fullBatchRetained :
    fullRetainedDeck r.before.source.palette.family (r.higherData G base hfour).ready.torsion
      (r.higherData G base hfour).input.signature ⊆ T.source.palette.family := by
  have retained := r.batchRetained G base
  rw [← (r.higherData G base hfour).paletteIdentity] at retained
  have member : (⟨(r.higherData G base hfour).input.m+2,
      (r.higherData G base hfour).input.signature⟩ : AnySignature (OI.K G)) ∈ r.before.source.palette.family := by
    simpa only [OccurrenceWorklist.initial] using (r.higherData G base hfour).input.retained
  change (OccurrenceBatch.palette G r.before.source.palette (r.higherData G base hfour).ready.torsion
    (r.higherData G base hfour).input.signature member (r.higherData G base hfour).input.proper).family ⊆ T.source.palette.family at retained
  rw [OccurrenceBatch.family_exact] at retained
  exact retained

private theorem paletteRoot_cast {P Q : Palette G} (identity : P = Q) (i : Fin P.count) :
    Frontier.paletteRoot G Q (Fin.cast (congrArg Palette.count identity) i) = Frontier.paletteRoot G P i := by
  cases identity
  rfl

/-- These integer labels are computed from the SAME actual after-batch suffix. -/
def PreparationReceipt.batchLabels : Fin (r.oldBatch G base hfour).count → Fin T.source.palette.count :=
  fun i => r.suffix.copyLabel G base (Fin.cast (congrArg Palette.count (r.oldBatchAfter G base hfour)) i)

theorem PreparationReceipt.batchLabels_saved (i : Fin (r.oldBatch G base hfour).count) :
    Frontier.paletteRoot G T.source.palette (r.batchLabels G base hfour i) = Frontier.paletteRoot G (r.oldBatch G base hfour) i :=
  (r.suffix.copyLabel_saved G base _).trans (paletteRoot_cast G (r.oldBatchAfter G base hfour) i)

theorem PreparationReceipt.selectedSignatureFinal :
    (⟨(r.higherData G base hfour).input.m+2,(r.higherData G base hfour).input.signature⟩ : AnySignature (OI.K G)) =
      (CurrentOccurrences.savedLeaf G T.source.palette q).1 :=
  (r.higherData G base hfour).input.literal.trans (congrArg Sigma.fst r.leafExact).symm

/-- Actual current-group raw-key access at FINAL table Q plus one literal raw
signature. It uses the copied old root and internally computed original-L scalar. -/
def PreparationReceipt.currentRawAccess
    (k : RawCardKey (r.higherData G base hfour).input.m (completeGroup T.source.palette.family T.ready.torsion)) :
    CurrentSignatureAccess G T.source.palette
      ⟨(r.higherData G base hfour).input.m,
        rawCard T.source.palette.family T.ready.torsion (r.higherData G base hfour).input.signature k⟩ :=
  GeneratedDeckTransport.copiedRawAccess G r.before.source.palette T.source.palette r.sourceRetained
    (r.higherData G base hfour).ready.torsion T.ready.torsion r.currentGroup
    (r.higherData G base hfour).input.signature k (r.higherData G base hfour).input.retained
    (r.higherData G base hfour).input.proper (r.batchLabels G base hfour) (r.batchLabels_saved G base hfour)

/-- Complete actual rawDeck access, including its zero sentinel, with no
minimum/core/local theorem, future palette or programme producer argument. -/
def PreparationReceipt.currentRawDeckAccess
    (g : Signature (OI.K G) (r.higherData G base hfour).input.m)
    (member : g ∈ rawDeck T.source.palette.family T.ready.torsion (r.higherData G base hfour).input.signature) :
    CurrentSignatureAccess G T.source.palette ⟨(r.higherData G base hfour).input.m,g⟩ :=
  GeneratedDeckTransport.copiedRawDeckAccess G r.before.source.palette T.source.palette r.sourceRetained
    (r.higherData G base hfour).ready.torsion T.ready.torsion r.currentGroup
    (r.higherData G base hfour).input.signature (r.higherData G base hfour).input.retained
    (r.higherData G base hfour).input.proper (r.batchLabels G base hfour) (r.batchLabels_saved G base hfour) g member

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupWorklist
