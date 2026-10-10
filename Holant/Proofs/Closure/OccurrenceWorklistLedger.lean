import Holant.Proofs.Closure.OccurrenceWorklistExecution

/-! Exact counted address coverage and cumulative copying of every source
label. In particular labels installed by one batch remain saved, with their
whole trees, throughout all later occurrence preparations. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceWorklist
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)

def Transition.copyLabel {S T : State G base} (e : Transition G base S T) :
    Fin S.palette.count → Fin T.palette.count := by
  cases e with
  | binary o hp ready hr h2 => exact id
  | higher o hp ready hr b => exact RetainedCatalogue.oldLabel G S.palette ready.torsion b.signature

theorem Transition.copyLabel_injective {S T : State G base} (e : Transition G base S T) :
    Function.Injective (e.copyLabel G base) := by
  cases e with
  | binary => exact Function.injective_id
  | higher o hp ready hr b =>
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin (RetainedCatalogue.count G S.palette ready.torsion b.signature) => x.val) h)

theorem Transition.copyLabel_saved {S T : State G base} (e : Transition G base S T)
    (i : Fin S.palette.count) :
    Frontier.paletteRoot G T.palette (e.copyLabel G base i) = Frontier.paletteRoot G S.palette i := by
  cases e with
  | binary => rfl
  | higher o hp ready hr b => exact RetainedCatalogue.old_saved G S.palette ready.torsion b.signature i

def Trace.copyLabel {S T : State G base} (h : Trace G base S T) :
    Fin S.palette.count → Fin T.palette.count :=
  match h with
  | .nil _ => id
  | .cons e _ rest => rest.copyLabel ∘ e.copyLabel G base

theorem Trace.copyLabel_injective {S T : State G base} (h : Trace G base S T) :
    Function.Injective (h.copyLabel G base) := by
  induction h with
  | nil => exact Function.injective_id
  | cons e work rest ih => exact ih.comp (e.copyLabel_injective G base)

theorem Trace.copyLabel_saved {S T : State G base} (h : Trace G base S T)
    (i : Fin S.palette.count) :
    Frontier.paletteRoot G T.palette (h.copyLabel G base i) = Frontier.paletteRoot G S.palette i := by
  induction h with
  | nil => rfl
  | cons e work rest ih => exact (ih (e.copyLabel G base i)).trans (e.copyLabel_saved G base i)

/-- Every earlier current occurrence has an injectively transported exact
saved address at the final CURRENT source, including newly installed labels. -/
def Trace.copyOccurrence {S T : State G base} (h : Trace G base S T)
    (o : CurrentOccurrences.Id G S.palette) : CurrentOccurrences.Id G T.palette :=
  ⟨h.copyLabel G base o.1,Occurrences.transportAddress (h.copyLabel_saved G base o.1).symm o.2⟩

theorem Trace.copyOccurrence_leaf {S T : State G base} (h : Trace G base S T)
    (o : CurrentOccurrences.Id G S.palette) :
    CurrentOccurrences.savedLeaf G T.palette (h.copyOccurrence G base o) =
      CurrentOccurrences.savedLeaf G S.palette o :=
  Occurrences.transportAddress_leaf (h.copyLabel_saved G base o.1).symm o.2

theorem Trace.copyOccurrence_injective {S T : State G base} (h : Trace G base S T) :
    Function.Injective (h.copyOccurrence G base) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ he
  have hi : h.copyLabel G base i = h.copyLabel G base j := congrArg Sigma.fst he
  have hij := h.copyLabel_injective G base hi
  subst j
  have hp : Occurrences.transportAddress (h.copyLabel_saved G base i).symm p =
      Occurrences.transportAddress (h.copyLabel_saved G base i).symm q :=
    @sigma_mk_injective (Fin T.palette.count)
      (fun k => Occurrences.Address (T.palette.trees k)) (h.copyLabel G base i) _ _ he
  exact Sigma.ext rfl (heq_of_eq (Occurrences.transportAddress_injective (h.copyLabel_saved G base i).symm hp))

theorem Trace.counted_coverage {S T : State G base} (h : Trace G base S T) :
    (h.visited G base).length + T.todo.card = S.todo.card := by
  induction h with
  | nil => simp [Trace.visited]
  | @cons S T U e work rest ih =>
    have he : T.todo.card + 1 = S.todo.card := by
      rw [e.after_todo G base]
      exact Finset.card_erase_add_one (e.selected_pending G base)
    change ((rest.visited G base).length + 1) + U.todo.card = S.todo.card
    omega

theorem Result.counted_coverage (R : Result G base) :
    (R.trace.visited G base).length + R.finalState.todo.card = Fintype.card (CurrentOccurrences.Id G base) := by
  simpa [initial] using R.trace.counted_coverage G base

theorem Result.pending_not_visited (R : Result G base) (o : CurrentOccurrences.Id G base)
    (hp : o ∈ R.finalState.todo) : o ∉ R.trace.visited G base := by
  intro hv
  exact R.trace.visited_not_final G base o hv hp

theorem Result.generated_coverage (R : Result G base) (o : CurrentOccurrences.Id G base) :
    o ∈ R.finalState.todo ∨
      ∃ A B, ∃ e : Transition G base A B, EventIn G base R.trace e ∧
        e.selected G base = o ∧ Nonempty (EventWork G base e) := by
  rcases R.coverage G base o with hp | hv
  · exact .inl hp
  · obtain ⟨A,B,e,he,hselected⟩ := R.trace.visited_event G base o hv
    exact .inr ⟨A,B,e,he,hselected,recorded_work G base R.trace e he⟩

theorem Result.exhaustive (R : Result G base) (empty : R.finalState.todo = ∅) :
    (R.trace.visited G base).toFinset = Finset.univ := by
  apply Finset.ext
  intro o
  simp only [Finset.mem_univ, iff_true, List.mem_toFinset]
  rcases R.coverage G base o with hp | hv
  · rw [empty] at hp
    exact False.elim (Finset.notMem_empty o hp)
  · exact hv

/-- Event work retains the selected pending local domain at that event's
literal current palette; being batch-prepared does not settle classification. -/
def EventWork.domain {S T : State G base} {e : Transition G base S T} (r : EventWork G base e) :
    CurrentOccurrences.Domain G S.palette (S.currentId G base (e.selected G base)) := by
  cases e with
  | binary o hp ready hr h2 => exact BinaryReceipt.domain r
  | higher o hp ready hr b => exact BatchReceipt.domain r

theorem EventWork.domainIdentity {S T : State G base} {e : Transition G base S T} (r : EventWork G base e) :
    r.domain G base = e.domain G base := by
  cases e with
  | binary o hp ready hr h2 => exact BinaryReceipt.domainIdentity r
  | higher o hp ready hr b => exact BatchReceipt.domainIdentity r

theorem EventWork.domain_pending {S T : State G base} {e : Transition G base S T} (r : EventWork G base e) :
    (r.domain G base).preparation = Frontier.Preparation.pending := by
  rw [r.domainIdentity G base]
  rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceWorklist
