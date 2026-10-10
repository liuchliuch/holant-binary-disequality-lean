import Holant.Proofs.Closure.GeneratedGroupWorklistExecution

/-! Exhausted-group provenance: every CURRENT saved prime has a real stored
preparation event at the FINAL complete group. Strict-growth resets discard
old preparation status; exact tree/address transport remains injective. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupWorklist
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)

def Transition.raw {S T : Active G base} (e : Transition G base S T) : Source G base := by
  cases e with
  | same raw event work ready hr hg => exact raw
  | growth raw event work ready hr hg => exact raw

def Transition.preparation {S T : Active G base} (e : Transition G base S T) :
    GeneratedOccurrenceWorklist.Transition G base S.source (e.raw G base) := by
  cases e with
  | same raw event work ready hr hg => exact event
  | growth raw event work ready hr hg => exact event

def Transition.storedWork {S T : Active G base} (e : Transition G base S T) :
    GeneratedOccurrenceWorklist.EventWork G base (e.preparation G base) := by
  cases e with
  | same raw event work ready hr hg => exact work
  | growth raw event work ready hr hg => exact work

def Transition.selected {S T : Active G base} (e : Transition G base S T) := (e.preparation G base).selected G base

def Transition.copyId {S T : Active G base} (e : Transition G base S T) :
    CurrentOccurrences.Id G S.source.palette → CurrentOccurrences.Id G T.source.palette := by
  cases e with
  | same raw event work ready hr hg => exact event.copyId G base
  | growth raw event work ready hr hg => exact event.copyId G base

theorem Transition.copyId_injective {S T : Active G base} (e : Transition G base S T) :
    Function.Injective (e.copyId G base) := by
  cases e with
  | same raw event work ready hr hg => exact event.copyId_injective G base
  | growth raw event work ready hr hg => exact event.copyId_injective G base

theorem Transition.copyId_leaf {S T : Active G base} (e : Transition G base S T)
    (o : CurrentOccurrences.Id G S.source.palette) :
    CurrentOccurrences.savedLeaf G T.source.palette (e.copyId G base o) =
      CurrentOccurrences.savedLeaf G S.source.palette o := by
  cases e with
  | same raw event work ready hr hg => exact event.copyId_leaf G base o
  | growth raw event work ready hr hg => exact event.copyId_leaf G base o

theorem Transition.retains {S T : Active G base} (e : Transition G base S T) :
    S.source.palette.family ⊆ T.source.palette.family := by
  cases e with
  | same raw event work ready hr hg => exact GeneratedGroupWorklist.retains G base (T := raw) event
  | growth raw event work ready hr hg => exact GeneratedGroupWorklist.retains G base (T := raw) event

/-- If a preparation remains done across an edge then that edge is genuinely
same-group. A strict-growth edge has empty done and cannot provide this premise. -/
theorem Transition.done_preimage {S T : Active G base} (e : Transition G base S T)
    (q : CurrentOccurrences.Id G T.source.palette) (hq : q ∈ T.source.done) :
    ∃ o : CurrentOccurrences.Id G S.source.palette,
      (o = e.selected G base ∨ o ∈ S.source.done) ∧ e.copyId G base o = q ∧
      completeGroup T.source.palette.family T.ready.torsion = completeGroup S.source.palette.family S.ready.torsion := by
  cases e with
  | same raw event work ready hr hg =>
    obtain ⟨o,ho,he⟩ := event.done_preimage G base q hq
    exact ⟨o,ho,he,hg⟩
  | growth raw event work ready hr hg => exact False.elim (Finset.notMem_empty q hq)

theorem same_never_reopens (S : Active G base) (raw : Source G base)
    (event : GeneratedOccurrenceWorklist.Transition G base S.source raw)
    (q : CurrentOccurrences.Id G S.source.palette) (hq : q ∈ S.source.done) : event.copyId G base q ∉ raw.todo :=
  fun hp => Finset.disjoint_left.mp raw.disjoint hp (event.copyId_done G base q hq)

def Trace.copyId {S T : Active G base} (h : Trace G base S T) :
    CurrentOccurrences.Id G S.source.palette → CurrentOccurrences.Id G T.source.palette :=
  match h with
  | .nil _ => id
  | .cons e rest => rest.copyId ∘ e.copyId G base

theorem Trace.copyId_injective {S T : Active G base} (h : Trace G base S T) : Function.Injective (h.copyId G base) := by
  induction h with
  | nil => exact Function.injective_id
  | cons e rest ih => exact ih.comp (e.copyId_injective G base)

theorem Trace.copyId_leaf {S T : Active G base} (h : Trace G base S T)
    (o : CurrentOccurrences.Id G S.source.palette) :
    CurrentOccurrences.savedLeaf G T.source.palette (h.copyId G base o) = CurrentOccurrences.savedLeaf G S.source.palette o := by
  induction h with
  | nil => rfl
  | cons e rest ih => exact (ih (e.copyId G base o)).trans (e.copyId_leaf G base o)

theorem Trace.retains {S T : Active G base} (h : Trace G base S T) : S.source.palette.family ⊆ T.source.palette.family := by
  induction h with
  | nil => exact fun _ h => h
  | cons e rest ih => exact (e.retains G base).trans ih

def Trace.append {S T U : Active G base} (h : Trace G base S T) (rest : Trace G base T U) : Trace G base S U :=
  match h with
  | .nil _ => rest
  | .cons e tail => .cons e (tail.append rest)

inductive EventIn : {S T : Active G base} → Trace G base S T → {A B : Active G base} → Transition G base A B → Prop
  | head {S T U} (e : Transition G base S T) (rest : Trace G base T U) : EventIn (.cons e rest) e
  | tail {S T U A B} (e : Transition G base S T) (rest : Trace G base T U) (actual : Transition G base A B)
      (recorded : EventIn rest actual) : EventIn (.cons e rest) actual

inductive Prepared : {S T : Active G base} → Trace G base S T → CurrentOccurrences.Id G T.source.palette → Prop
  | head {S T U} (e : Transition G base S T) (rest : Trace G base T U)
      (currentGroup : completeGroup U.source.palette.family U.ready.torsion =
        completeGroup S.source.palette.family S.ready.torsion) :
      Prepared (.cons e rest) (rest.copyId G base (e.copyId G base (e.selected G base)))
  | tail {S T U} (e : Transition G base S T) (rest : Trace G base T U)
      (q : CurrentOccurrences.Id G U.source.palette) (prepared : Prepared rest q) : Prepared (.cons e rest) q

theorem Trace.done_covered {S T : Active G base} (h : Trace G base S T)
    (q : CurrentOccurrences.Id G T.source.palette) (hq : q ∈ T.source.done) :
    (∃ o, o ∈ S.source.done ∧ h.copyId G base o = q ∧
      completeGroup T.source.palette.family T.ready.torsion = completeGroup S.source.palette.family S.ready.torsion) ∨
        Prepared G base h q := by
  induction h with
  | nil => exact .inl ⟨q,hq,rfl,rfl⟩
  | cons e rest ih =>
    rcases ih q hq with ⟨p,hp,he,hg⟩ | prepared
    · obtain ⟨o,hs,ho,hm⟩ := e.done_preimage G base p hp
      rcases hs with rfl | old
      · right
        rw [← he,← ho]
        exact .head e rest (hg.trans hm)
      · exact .inl ⟨o,old,(congrArg (rest.copyId G base) ho).trans he,hg.trans hm⟩
    · exact .inr (.tail e rest q prepared)

theorem Prepared.split {S T : Active G base} {h : Trace G base S T} {q : CurrentOccurrences.Id G T.source.palette}
    (prepared : Prepared G base h q) :
    ∃ A B, ∃ prior : Trace G base S A, ∃ e : Transition G base A B, ∃ suffix : Trace G base B T,
      h = prior.append G base (.cons e suffix) ∧ EventIn G base h e ∧
        suffix.copyId G base (e.copyId G base (e.selected G base)) = q ∧
        completeGroup T.source.palette.family T.ready.torsion = completeGroup A.source.palette.family A.ready.torsion := by
  induction prepared with
  | head e rest group => exact ⟨_,_,.nil _,e,rest,rfl,.head e rest,rfl,group⟩
  | tail e rest q hp ih =>
    obtain ⟨A,B,prior,actual,suffix,hex,recorded,he,hg⟩ := ih
    exact ⟨A,B,.cons e prior,actual,suffix,congrArg (fun r => Trace.cons e r) hex,.tail e rest actual recorded,he,hg⟩

structure PreparationReceipt {S T : Active G base} (h : Trace G base S T)
    (q : CurrentOccurrences.Id G T.source.palette) : Type 1 where
  before : Active G base
  after : Active G base
  prior : Trace G base S before
  event : Transition G base before after
  suffix : Trace G base after T
  exactTrace : h = prior.append G base (.cons event suffix)
  recorded : EventIn G base h event
  selectedFinal : suffix.copyId G base (event.copyId G base (event.selected G base)) = q
  leafExact : CurrentOccurrences.savedLeaf G T.source.palette q =
    CurrentOccurrences.savedLeaf G before.source.palette (event.selected G base)
  currentGroup : completeGroup T.source.palette.family T.ready.torsion =
    completeGroup before.source.palette.family before.ready.torsion
  sourceRetained : before.source.palette.family ⊆ T.source.palette.family

def PreparationReceipt.storedWork {S T : Active G base} {h : Trace G base S T}
    {q : CurrentOccurrences.Id G T.source.palette} (r : PreparationReceipt G base h q) := r.event.storedWork G base

theorem Prepared.receipt_nonempty {S T : Active G base} {h : Trace G base S T} {q : CurrentOccurrences.Id G T.source.palette}
    (hp : Prepared G base h q) : Nonempty (PreparationReceipt G base h q) := by
  obtain ⟨A,B,prior,e,suffix,hex,recorded,selected,hg⟩ := hp.split G base
  refine ⟨⟨A,B,prior,e,suffix,hex,recorded,selected,?_,hg,(e.retains G base).trans (suffix.retains G base)⟩⟩
  rw [← selected]
  exact (suffix.copyId_leaf G base _).trans (e.copyId_leaf G base _)

def preparedReceipt {S T : Active G base} {h : Trace G base S T} {q : CurrentOccurrences.Id G T.source.palette}
    (hp : Prepared G base h q) : PreparationReceipt G base h q := Classical.choice (hp.receipt_nonempty G base)

def Exhausted.preparationReceipt {S : Active G base} (r : Exhausted G base S) (noPrior : S.source.done = ∅)
    (q : CurrentOccurrences.Id G r.final.source.palette) : PreparationReceipt G base r.trace q := by
  have hq : q ∈ r.final.source.done := by rw [r.done_complete G base]; exact Finset.mem_univ _
  have hp : Prepared G base r.trace q := by
    rcases r.trace.done_covered G base q hq with ⟨o,ho,_,_⟩ | hp
    · rw [noPrior] at ho
      exact False.elim (Finset.notMem_empty o ho)
    · exact hp
  exact preparedReceipt G base hp

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupWorklist
