import Holant.Proofs.Closure.QueueDeck
import Holant.Proofs.Closure.ProgrammeRetained

/-! Closed complete-batch assembly. Both physical programmes, the retained
catalogue and the constructor-indexed initial-to-final trace are produced
internally from the same current palette, exact full keys and once-saved trees.
The stronger event-indexed physical receipts are exported separately. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.QueueBatch
open Holant Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature Holant.Tractable.AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)

/-- No new palette programme or queue coverage policy is an input. -/
def result (hm : 2 ≤ m) : DeckBatchResult G P torsion f where
  palette := ProgrammeRetained.palette G P torsion f core hcore hm
  oldSaved i := ⟨RetainedCatalogue.oldLabel G P torsion f i,
    RetainedCatalogue.old_saved G P torsion f i⟩
  deckSaved k := ⟨RetainedCatalogue.deckLabel G P torsion f k,
    RetainedCatalogue.deck_saved G P torsion f k⟩
  finalQueue := FullQueue.finalQueue G P torsion f
  queueRun := FullQueue.initial_to_final G P torsion f
  exhausted := FullQueue.exhausted G P torsion f
  allDone := FullQueue.allDone G P torsion f

theorem complete_deck_batch : CompleteDeckBatchGoal := by
  intro s a G P torsion m f core hm _he hcore
  exact ⟨result G P torsion f core hcore hm⟩

/-- Exact final palette identity, not merely an existential augmented carrier. -/
@[simp] theorem result_palette (hm : 2 ≤ m) :
    (result G P torsion f core hcore hm).palette =
      ProgrammeRetained.palette G P torsion f core hcore hm := rfl

/-- Exact final queue identity with the internally constructed inspection trace. -/
@[simp] theorem result_queue (hm : 2 ≤ m) :
    (result G P torsion f core hcore hm).finalQueue =
      (FullQueue.execution G P torsion f).finalQueue := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.QueueBatch
end
