import Holant.Proofs.Closure.GeneratedGroupWorklistLedger

/-! Full copied-root/table transport through the actual group-restarting trace,
including every intermediate batch label. Reset changes preparation status only;
it does not change the returned physical palette or its saved occurrences. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupWorklist
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)

def preparationCopyLabel {S T : Source G base} (e : GeneratedOccurrenceWorklist.Transition G base S T) :
    Fin S.palette.count → Fin T.palette.count := by
  cases e with
  | binary o hp ready hr h2 => exact id
  | higher o hp ready hr b => exact RetainedCatalogue.oldLabel G S.palette ready.torsion b.signature

theorem preparationCopyLabel_saved {S T : Source G base} (e : GeneratedOccurrenceWorklist.Transition G base S T)
    (i : Fin S.palette.count) : Frontier.paletteRoot G T.palette (preparationCopyLabel G base e i) =
      Frontier.paletteRoot G S.palette i := by
  cases e with
  | binary => rfl
  | higher o hp ready hr b => exact RetainedCatalogue.old_saved G S.palette ready.torsion b.signature i

theorem preparationCopyLabel_injective {S T : Source G base} (e : GeneratedOccurrenceWorklist.Transition G base S T) :
    Function.Injective (preparationCopyLabel G base e) := by
  cases e with
  | binary => exact Function.injective_id
  | higher o hp ready hr b =>
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin (RetainedCatalogue.count G S.palette ready.torsion b.signature) => x.val) h)

def Transition.copyLabel {S T : Active G base} (e : Transition G base S T) :
    Fin S.source.palette.count → Fin T.source.palette.count := by
  cases e with
  | same raw event work ready hr hg => exact preparationCopyLabel G base (T := raw) event
  | growth raw event work ready hr hg => exact preparationCopyLabel G base (T := raw) event

theorem Transition.copyLabel_saved {S T : Active G base} (e : Transition G base S T)
    (i : Fin S.source.palette.count) : Frontier.paletteRoot G T.source.palette (e.copyLabel G base i) =
      Frontier.paletteRoot G S.source.palette i := by
  cases e with
  | same raw event work ready hr hg => exact preparationCopyLabel_saved G base event i
  | growth raw event work ready hr hg => exact preparationCopyLabel_saved G base event i

theorem Transition.copyLabel_injective {S T : Active G base} (e : Transition G base S T) :
    Function.Injective (e.copyLabel G base) := by
  cases e with
  | same raw event work ready hr hg => exact preparationCopyLabel_injective G base event
  | growth raw event work ready hr hg => exact preparationCopyLabel_injective G base event

@[simp] theorem Transition.raw_paletteIdentity {S T : Active G base} (e : Transition G base S T) :
    (e.raw G base).palette = T.source.palette := by cases e <;> rfl

def Trace.copyLabel {S T : Active G base} (h : Trace G base S T) :
    Fin S.source.palette.count → Fin T.source.palette.count :=
  match h with
  | .nil _ => id
  | .cons e rest => rest.copyLabel ∘ e.copyLabel G base

theorem Trace.copyLabel_saved {S T : Active G base} (h : Trace G base S T)
    (i : Fin S.source.palette.count) : Frontier.paletteRoot G T.source.palette (h.copyLabel G base i) =
      Frontier.paletteRoot G S.source.palette i := by
  induction h with
  | nil => rfl
  | cons e rest ih => exact (ih (e.copyLabel G base i)).trans (e.copyLabel_saved G base i)

theorem Trace.copyLabel_injective {S T : Active G base} (h : Trace G base S T) : Function.Injective (h.copyLabel G base) := by
  induction h with
  | nil => exact Function.injective_id
  | cons e rest ih => exact ih.comp (e.copyLabel_injective G base)

def PreparationReceipt.labels {S T : Active G base} {h : Trace G base S T}
    {q : CurrentOccurrences.Id G T.source.palette} (r : PreparationReceipt G base h q) :
    Fin r.before.source.palette.count → Fin T.source.palette.count :=
  (Trace.cons r.event r.suffix).copyLabel G base

theorem PreparationReceipt.labels_saved {S T : Active G base} {h : Trace G base S T}
    {q : CurrentOccurrences.Id G T.source.palette} (r : PreparationReceipt G base h q)
    (i : Fin r.before.source.palette.count) :
    Frontier.paletteRoot G T.source.palette (r.labels G base i) = Frontier.paletteRoot G r.before.source.palette i :=
  (Trace.cons r.event r.suffix).copyLabel_saved G base i

theorem PreparationReceipt.labels_injective {S T : Active G base} {h : Trace G base S T}
    {q : CurrentOccurrences.Id G T.source.palette} (r : PreparationReceipt G base h q) : Function.Injective (r.labels G base) :=
  (Trace.cons r.event r.suffix).copyLabel_injective G base

theorem PreparationReceipt.labels_table {S T : Active G base} {h : Trace G base S T}
    {q : CurrentOccurrences.Id G T.source.palette} (r : PreparationReceipt G base h q)
    (i : Fin r.before.source.palette.count) :
    (⟨T.source.palette.arity (r.labels G base i).val,T.source.palette.table (r.labels G base i)⟩ : AnySignature (OI.K G)) =
      ⟨r.before.source.palette.arity i.val,r.before.source.palette.table i⟩ := congrArg Sigma.fst (r.labels_saved G base i)

theorem PreparationReceipt.afterRetained {S T : Active G base} {h : Trace G base S T}
    {q : CurrentOccurrences.Id G T.source.palette} (r : PreparationReceipt G base h q) :
    r.after.source.palette.family ⊆ T.source.palette.family := r.suffix.retains G base

theorem PreparationReceipt.batchRetained {S T : Active G base} {h : Trace G base S T}
    {q : CurrentOccurrences.Id G T.source.palette} (r : PreparationReceipt G base h q) :
    (r.event.raw G base).palette.family ⊆ T.source.palette.family := by
  rw [r.event.raw_paletteIdentity G base]
  exact r.afterRetained G base

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupWorklist
