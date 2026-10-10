import Holant.Proofs.Closure.GeneratedOccurrenceWorklistExecution

/-! Actual-event lineage for every prepared CURRENT saved occurrence.
Every final done address is copied injectively through an actual suffix from
an actual selected source address with its stored work. This proves preparation
at the event's current group, not final-group deck saturation or classification. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklist
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)

def Transition.copyId {S T : State G base} (e : Transition G base S T) :
    CurrentOccurrences.Id G S.palette → CurrentOccurrences.Id G T.palette := by
  cases e with
  | binary o hp ready hr h2 => exact id
  | higher o hp ready hr b => exact fun q => copy G S.palette ready.torsion b.signature b.retained b.proper q

theorem Transition.copyId_injective {S T : State G base} (e : Transition G base S T) :
    Function.Injective (e.copyId G base) := by
  cases e with
  | binary => exact Function.injective_id
  | higher o hp ready hr b => exact (copy G S.palette ready.torsion b.signature b.retained b.proper).injective

theorem Transition.copyId_leaf {S T : State G base} (e : Transition G base S T)
    (o : CurrentOccurrences.Id G S.palette) :
    CurrentOccurrences.savedLeaf G T.palette (e.copyId G base o) = CurrentOccurrences.savedLeaf G S.palette o := by
  cases e with
  | binary => rfl
  | higher selected hp ready hr b =>
    exact GeneratedOccurrenceWorklistPartition.copyId_leaf G S.palette ready.torsion b.signature b.retained b.proper o

theorem Transition.copyId_done {S T : State G base} (e : Transition G base S T)
    (o : CurrentOccurrences.Id G S.palette) (ho : o ∈ S.done) : e.copyId G base o ∈ T.done := by
  cases e with
  | binary => exact Finset.mem_insert_of_mem ho
  | higher selected hp ready hr b => exact Finset.mem_map.mpr ⟨o,Finset.mem_insert_of_mem ho,rfl⟩

theorem Transition.done_preimage {S T : State G base} (e : Transition G base S T)
    (q : CurrentOccurrences.Id G T.palette) (hq : q ∈ T.done) :
    ∃ o : CurrentOccurrences.Id G S.palette, (o = e.selected G base ∨ o ∈ S.done) ∧ e.copyId G base o = q := by
  cases e with
  | binary o hp ready hr h2 => exact ⟨q,Finset.mem_insert.mp hq,rfl⟩
  | higher o hp ready hr b =>
    obtain ⟨p,hp,he⟩ := Finset.mem_map.mp hq
    exact ⟨p,Finset.mem_insert.mp hp,he⟩

def Trace.copyId {S T : State G base} (h : Trace G base S T) :
    CurrentOccurrences.Id G S.palette → CurrentOccurrences.Id G T.palette :=
  match h with
  | .nil _ => id
  | .cons e _ rest => rest.copyId ∘ e.copyId G base

theorem Trace.copyId_injective {S T : State G base} (h : Trace G base S T) : Function.Injective (h.copyId G base) := by
  induction h with
  | nil => exact Function.injective_id
  | cons e work rest ih => exact ih.comp (e.copyId_injective G base)

theorem Trace.copyId_leaf {S T : State G base} (h : Trace G base S T) (o : CurrentOccurrences.Id G S.palette) :
    CurrentOccurrences.savedLeaf G T.palette (h.copyId G base o) = CurrentOccurrences.savedLeaf G S.palette o := by
  induction h with
  | nil => rfl
  | cons e work rest ih => exact (ih (e.copyId G base o)).trans (e.copyId_leaf G base o)

theorem Trace.copyId_done {S T : State G base} (h : Trace G base S T)
    (o : CurrentOccurrences.Id G S.palette) (ho : o ∈ S.done) : h.copyId G base o ∈ T.done := by
  induction h with
  | nil => exact ho
  | cons e work rest ih => exact ih _ (e.copyId_done G base o ho)

def Trace.append {S T U : State G base} (h : Trace G base S T) (rest : Trace G base T U) : Trace G base S U :=
  match h with
  | .nil _ => rest
  | .cons e work tail => .cons e work (tail.append rest)

/-- A final prepared address is the selected address of an actual event,
injectively copied through that event and the SAME recorded suffix. -/
inductive Prepared : {S T : State G base} → Trace G base S T → CurrentOccurrences.Id G T.palette → Prop
  | head {S T U} (e : Transition G base S T) (w : EventWork G base e) (rest : Trace G base T U) :
      Prepared (.cons e w rest) (rest.copyId G base (e.copyId G base (e.selected G base)))
  | tail {S T U} (e : Transition G base S T) (w : EventWork G base e) (rest : Trace G base T U)
      (q : CurrentOccurrences.Id G U.palette) (prepared : Prepared rest q) : Prepared (.cons e w rest) q

theorem Trace.done_covered {S T : State G base} (h : Trace G base S T)
    (q : CurrentOccurrences.Id G T.palette) (hq : q ∈ T.done) :
    (∃ o, o ∈ S.done ∧ h.copyId G base o = q) ∨ Prepared G base h q := by
  induction h with
  | nil => exact .inl ⟨q,hq,rfl⟩
  | cons e w rest ih =>
    rcases ih q hq with ⟨p,hp,he⟩ | prepared
    · obtain ⟨o,hs,ho⟩ := e.done_preimage G base p hp
      rcases hs with rfl | old
      · right
        rw [← he,← ho]
        exact .head e w rest
      · exact .inl ⟨o,old,(congrArg (rest.copyId G base) ho).trans he⟩
    · exact .inr (.tail e w rest q prepared)

/-- Full trace decomposition retains the work data actually stored on the
chosen event, rather than any unrelated inhabitant of its receipt type. -/
theorem Prepared.split {S T : State G base} {h : Trace G base S T} {q : CurrentOccurrences.Id G T.palette}
    (prepared : Prepared G base h q) :
    ∃ A B, ∃ prior : Trace G base S A, ∃ e : Transition G base A B,
      ∃ w : EventWork G base e, ∃ suffix : Trace G base B T,
        h = prior.append G base (.cons e w suffix) ∧ EventIn G base h e ∧
        suffix.copyId G base (e.copyId G base (e.selected G base)) = q := by
  induction prepared with
  | head e w rest => exact ⟨_,_,.nil _,e,w,rest,rfl,.head e w rest,rfl⟩
  | tail e w rest q prepared ih =>
    obtain ⟨A,B,prior,actual,actualWork,suffix,hex,he,hq⟩ := ih
    refine ⟨A,B,.cons e w prior,actual,actualWork,suffix,?_,.tail e w rest actual he,hq⟩
    exact congrArg (fun r => Trace.cons e w r) hex

structure PreparationReceipt {S T : State G base} (h : Trace G base S T) (q : CurrentOccurrences.Id G T.palette) : Type 1 where
  before : State G base
  after : State G base
  prior : Trace G base S before
  event : Transition G base before after
  storedWork : EventWork G base event
  suffix : Trace G base after T
  exactTrace : h = prior.append G base (.cons event storedWork suffix)
  recorded : EventIn G base h event
  selectedFinal : suffix.copyId G base (event.copyId G base (event.selected G base)) = q
  leafExact : CurrentOccurrences.savedLeaf G T.palette q =
    CurrentOccurrences.savedLeaf G before.palette (event.selected G base)

theorem Prepared.receipt_nonempty {S T : State G base} {h : Trace G base S T} {q : CurrentOccurrences.Id G T.palette}
    (hp : Prepared G base h q) : Nonempty (PreparationReceipt G base h q) := by
  obtain ⟨A,B,prior,e,w,suffix,hex,recorded,selectedFinal⟩ := hp.split G base
  refine ⟨⟨A,B,prior,e,w,suffix,hex,recorded,selectedFinal,?_⟩⟩
  rw [← selectedFinal]
  exact (suffix.copyId_leaf G base _).trans (e.copyId_leaf G base _)

def preparedReceipt {S T : State G base} {h : Trace G base S T} {q : CurrentOccurrences.Id G T.palette}
    (hp : Prepared G base h q) : PreparationReceipt G base h q := Classical.choice (hp.receipt_nonempty G base)

theorem Result.prepared_coverage (R : Result G base) (q : CurrentOccurrences.Id G (R.finalState G base).palette)
    (hq : q ∈ (R.finalState G base).done) : Prepared G base (R.trace G base) q := by
  rcases (R.trace G base).done_covered G base q hq with ⟨o,ho,_⟩ | hp
  · exact False.elim (Finset.notMem_empty o ho)
  · exact hp

def Result.preparationReceipt (R : Result G base) (q : CurrentOccurrences.Id G (R.finalState G base).palette)
    (hq : q ∈ (R.finalState G base).done) : PreparationReceipt G base (R.trace G base) q :=
  preparedReceipt G base (R.prepared_coverage G base q hq)

def Result.all_prepared (R : Result G base) (empty : (R.finalState G base).todo = ∅)
    (q : CurrentOccurrences.Id G (R.finalState G base).palette) : PreparationReceipt G base (R.trace G base) q :=
  R.preparationReceipt G base q (by rw [R.done_complete G base empty]; exact Finset.mem_univ _)

/-- Preparation status is separate from every current local classification. -/
inductive Status (R : Result G base) (q : CurrentOccurrences.Id G (R.finalState G base).palette) : Type 1
  | pending (unvisited : q ∈ (R.finalState G base).todo)
  | prepared (receipt : PreparationReceipt G base (R.trace G base) q)

def Result.status (R : Result G base) (q : CurrentOccurrences.Id G (R.finalState G base).palette) : Status G base R q := by
  by_cases ht : q ∈ (R.finalState G base).todo
  · exact .pending ht
  · have hd : q ∈ (R.finalState G base).done := by
      have hu : q ∈ (R.finalState G base).todo ∪ (R.finalState G base).done := by
        rw [(R.finalState G base).partition]
        exact Finset.mem_univ _
      exact (Finset.mem_union.mp hu).resolve_left ht
    exact .prepared (R.preparationReceipt G base q hd)

def EventWork.domain {S T : State G base} {e : Transition G base S T} (w : EventWork G base e) :
    CurrentOccurrences.Domain G S.palette (e.selected G base) := by
  cases e with
  | binary o hp ready hr h2 => exact BinaryReceipt.domain w
  | higher o hp ready hr b => exact OccurrenceWorklist.BatchReceipt.domain w

theorem EventWork.domain_pending {S T : State G base} {e : Transition G base S T} (w : EventWork G base e) :
    (w.domain G base).preparation = Frontier.Preparation.pending := by
  cases e with
  | binary o hp ready hr h2 =>
    change (BinaryReceipt.domain w).preparation = _
    rw [w.domainIdentity]
    rfl
  | higher o hp ready hr b =>
    exact OccurrenceWorklist.BatchReceipt.domain_pending G S.palette
      (OccurrenceWorklist.initial G S.palette) o b ready.torsion w

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklist
