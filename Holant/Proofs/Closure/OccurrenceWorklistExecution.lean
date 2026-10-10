import Holant.Proofs.Closure.OccurrenceWorklist

/-! An internally constructed finite cumulative occurrence schedule. The
separate outer measure is pending immutable IDs. Actual current-source work
and physical receipts are stored on every event; local goals stay pending. -/
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

/-- Both event kinds store a real recomputation of current eligibility.
Only higher-even visits run a new batch; binary visits retain the exact
current physical source and its pending binary domain. -/
inductive Transition : State G base → State G base → Type 1
  | binary (S : State G base) (o : CurrentOccurrences.Id G base) (pending : o ∈ S.todo)
      (ready : Ready G S.palette) (recomputed : inspect G S.palette = .inr ready)
      (arity : (CurrentOccurrences.savedLeaf G base o).1.1 = 2) :
      Transition S (S.erase G base o)
  | higher (S : State G base) (o : CurrentOccurrences.Id G base) (pending : o ∈ S.todo)
      (ready : Ready G S.palette) (recomputed : inspect G S.palette = .inr ready)
      (input : BatchInput G base S o) : Transition S (S.batch G base o input ready.torsion)

def Transition.selected {S T : State G base} : Transition G base S T → CurrentOccurrences.Id G base
  | .binary _ o _ _ _ _ => o
  | .higher _ o _ _ _ _ => o

theorem Transition.selected_pending {S T : State G base} (e : Transition G base S T) :
    e.selected G base ∈ S.todo := by cases e <;> assumption

theorem Transition.after_todo {S T : State G base} (e : Transition G base S T) :
    T.todo = S.todo.erase (e.selected G base) := by cases e <;> rfl

theorem Transition.decreases {S T : State G base} (e : Transition G base S T) :
    T.todo.card < S.todo.card := by
  rw [e.after_todo G base]
  exact Finset.card_erase_lt_of_mem (e.selected_pending G base)

def Transition.domain {S T : State G base} (e : Transition G base S T) :=
  S.domain G base (e.selected G base)

structure BinaryReceipt (S : State G base) (o : CurrentOccurrences.Id G base) : Type 1 where
  domain : CurrentOccurrences.Domain G S.palette (S.currentId G base o)
  domainIdentity : domain = S.domain G base o

def EventWork {S T : State G base} (e : Transition G base S T) : Type 1 := by
  cases e with
  | binary o hp ready hr h2 => exact BinaryReceipt G base S o
  | higher o hp ready hr input => exact BatchReceipt G base S o input ready.torsion

def eventWork {S T : State G base} (e : Transition G base S T) : EventWork G base e := by
  cases e with
  | binary o hp ready hr h2 => exact ⟨S.domain G base o,rfl⟩
  | higher o hp ready hr input => exact batchReceipt G base S o input ready.torsion

theorem ready_nonunary (S : State G base) (ready : Ready G S.palette)
    (o : CurrentOccurrences.Id G base) : (CurrentOccurrences.savedLeaf G base o).1.1 ≠ 1 := by
  let q := (CurrentOccurrences.savedLeaf G base o).1
  have hr : q ∈ S.palette.family := by
    change (CurrentOccurrences.savedLeaf G base o).1 ∈ S.palette.family
    rw [← S.leafExact G base o]
    exact CurrentOccurrences.savedLeaf_retained G S.palette (S.currentId G base o)
  have hp : Prime q := CurrentOccurrences.savedLeaf_prime G base o
  change q.1 ≠ 1
  rcases q with ⟨n,f⟩
  intro hn
  change n = 1 at hn
  subst n
  exact ready.noUnary ⟨f,hr,hp.1⟩

def next (S : State G base) (ready : Ready G S.palette) (recomputed : inspect G S.palette = .inr ready)
    (nonempty : S.todo.Nonempty) : Σ T, Transition G base S T := by
  let o := Classical.choose nonempty
  have pending : o ∈ S.todo := Classical.choose_spec nonempty
  by_cases h2 : (CurrentOccurrences.savedLeaf G base o).1.1 = 2
  · exact ⟨S.erase G base o,.binary S o pending ready recomputed h2⟩
  have h1 := ready_nonunary G base S ready o
  have hpos := CurrentOccurrences.savedLeaf_positive G base o
  have h3 : 3 ≤ (CurrentOccurrences.savedLeaf G base o).1.1 := by omega
  have he : Even (CurrentOccurrences.savedLeaf G base o).1.1 := by
    rw [← S.leafExact G base o]
    exact ready.noOdd _ (CurrentOccurrences.savedLeaf_retained G S.palette (S.currentId G base o))
      (CurrentOccurrences.savedLeaf_prime G S.palette (S.currentId G base o))
      (by rwa [S.leafExact G base o])
  have h4 : 4 ≤ (CurrentOccurrences.savedLeaf G base o).1.1 := by rcases he with ⟨k,hk⟩; omega
  let b := batchInput G base S o h4 he
  exact ⟨S.batch G base o b ready.torsion,.higher S o pending ready recomputed b⟩

inductive Trace : State G base → State G base → Type 1
  | nil (S : State G base) : Trace S S
  | cons {S T U : State G base} (event : Transition G base S T)
      (work : EventWork G base event) (rest : Trace T U) : Trace S U

def Trace.visited {S T : State G base} : Trace G base S T → List (CurrentOccurrences.Id G base)
  | .nil _ => []
  | .cons e _ rest => e.selected G base :: rest.visited

theorem Trace.no_reopen {S T : State G base} (h : Trace G base S T) : T.todo ⊆ S.todo := by
  induction h with
  | nil => exact fun _ h => h
  | cons e work rest ih =>
    rw [e.after_todo G base] at ih
    exact ih.trans (Finset.erase_subset _ _)

theorem Trace.visited_before {S T : State G base} (h : Trace G base S T) :
    ∀ o ∈ h.visited G base, o ∈ S.todo := by
  induction h with
  | nil => simp [Trace.visited]
  | cons e work rest ih =>
    intro o ho
    rcases List.mem_cons.mp ho with rfl | hr
    · exact e.selected_pending G base
    · have hm := ih o hr
      rw [e.after_todo G base] at hm
      exact (Finset.mem_erase.mp hm).2

theorem Trace.visited_not_final {S T : State G base} (h : Trace G base S T) :
    ∀ o ∈ h.visited G base, o ∉ T.todo := by
  induction h with
  | nil => simp [Trace.visited]
  | cons e work rest ih =>
    intro o ho
    rcases List.mem_cons.mp ho with rfl | hr
    · intro hf
      have hm := rest.no_reopen G base hf
      rw [e.after_todo G base] at hm
      exact Finset.notMem_erase _ _ hm
    · exact ih o hr

theorem Trace.visited_nodup {S T : State G base} (h : Trace G base S T) :
    (h.visited G base).Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | cons e work rest ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hm
    have hp := rest.visited_before G base _ hm
    rw [e.after_todo G base] at hp
    exact Finset.notMem_erase _ _ hp

theorem Trace.pending_or_visited {S T : State G base} (h : Trace G base S T) :
    ∀ o ∈ S.todo, o ∈ T.todo ∨ o ∈ h.visited G base := by
  induction h with
  | nil => exact fun _ ho => .inl ho
  | cons e work rest ih =>
    intro o ho
    by_cases he : o = e.selected G base
    · exact .inr (List.mem_cons.mpr (.inl he))
    · have ht : o ∈ _ := Finset.mem_erase.mpr ⟨he,ho⟩
      rw [← e.after_todo G base] at ht
      rcases ih o ht with hf | hv
      · exact .inl hf
      · exact .inr (List.mem_cons.mpr (.inr hv))

/-- A recorded event is indexed by the actual changing source state. -/
inductive EventIn : {S T : State G base} → Trace G base S T →
    {A B : State G base} → Transition G base A B → Prop
  | head {S T U} (e : Transition G base S T) (w : EventWork G base e) (r : Trace G base T U) :
      EventIn (.cons e w r) e
  | tail {S T U A B} (e : Transition G base S T) (w : EventWork G base e) (r : Trace G base T U)
      (actual : Transition G base A B) (recorded : EventIn r actual) : EventIn (.cons e w r) actual

theorem Trace.visited_event {S T : State G base} (h : Trace G base S T)
    (o : CurrentOccurrences.Id G base) (ho : o ∈ h.visited G base) :
    ∃ A B, ∃ e : Transition G base A B, EventIn G base h e ∧ e.selected G base = o := by
  induction h with
  | nil => simp [Trace.visited] at ho
  | cons e w r ih =>
    rcases List.mem_cons.mp ho with he | hr
    · exact ⟨_,_,e,.head e w r,he.symm⟩
    · obtain ⟨A,B,actual,hactual,he⟩ := ih hr
      exact ⟨A,B,actual,.tail e w r actual hactual,he⟩

theorem recorded_work {S T : State G base} (h : Trace G base S T)
    {A B : State G base} (e : Transition G base A B) (he : EventIn G base h e) :
    Nonempty (EventWork G base e) := by
  induction he with
  | head e w r => exact ⟨w⟩
  | tail e w r actual recorded ih => exact ih

inductive Execution : State G base → Type 1
  | exhausted (S : State G base) (empty : S.todo = ∅) : Execution S
  | structural (S : State G base) (stop : Stop G S.palette)
      (recomputed : inspect G S.palette = .inl stop) : Execution S
  | next {S T : State G base} (event : Transition G base S T) (work : EventWork G base event)
      (rest : Execution T) : Execution S

def finish (S : State G base) : Execution G base S :=
  (measure (fun S : State G base => S.todo.card)).wf.fix (fun S recurse =>
    match hi : inspect G S.palette with
    | .inl stop => .structural S stop hi
    | .inr ready =>
      if hn : S.todo.Nonempty then
        let e := next G base S ready hi hn
        .next e.2 (eventWork G base e.2) (recurse e.1 (e.2.decreases G base))
      else .exhausted S (Finset.not_nonempty_iff_eq_empty.mp hn)) S

def Execution.finalState {S : State G base} : Execution G base S → State G base
  | .exhausted S _ => S
  | .structural S _ _ => S
  | .next _ _ rest => rest.finalState

def Execution.trace {S : State G base} (h : Execution G base S) : Trace G base S (h.finalState G base) :=
  match h with
  | .exhausted S _ => .nil S
  | .structural S _ _ => .nil S
  | .next e work rest => .cons e work rest.trace

/-- Exhaustion prepares each immutable ID once; a genuine structural stop
leaves every remaining ID explicit. Neither outcome is global rigidity. -/
theorem Execution.outcome {S : State G base} (h : Execution G base S) :
    (h.finalState G base).todo = ∅ ∨ Nonempty (Stop G (h.finalState G base).palette) := by
  induction h with
  | exhausted S he => exact .inl he
  | structural S stop hr => exact .inr ⟨stop⟩
  | next e work rest ih => exact ih

structure Result where
  finalState : State G base
  trace : Trace G base (initial G base) finalState
  outcome : finalState.todo = ∅ ∨ Nonempty (Stop G finalState.palette)
  frontier : CurrentFrontier.Result G finalState.palette
  frontierIdentity : frontier = CurrentFrontier.build G finalState.palette

def result : Result G base :=
  let h := finish G base (initial G base)
  ⟨h.finalState G base,h.trace G base,h.outcome G base,
    CurrentFrontier.build G (h.finalState G base).palette,rfl⟩

theorem Result.coverage (R : Result G base) (o : CurrentOccurrences.Id G base) :
    o ∈ R.finalState.todo ∨ o ∈ R.trace.visited G base :=
  R.trace.pending_or_visited G base o (Finset.mem_univ o)

theorem Result.exact_once (R : Result G base) : (R.trace.visited G base).Nodup :=
  R.trace.visited_nodup G base

theorem Result.new_current_pending (R : Result G base) (o : CurrentOccurrences.Id G R.finalState.palette) :
    (⟨o,CurrentOccurrences.domain G R.finalState.palette o⟩ :
      (o : CurrentOccurrences.Id G R.finalState.palette) × CurrentOccurrences.Domain G R.finalState.palette o)
        ∈ R.frontier.pending := by
  rw [R.frontierIdentity]
  exact CurrentFrontier.build_current_coverage G R.finalState.palette o

end Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceWorklist
