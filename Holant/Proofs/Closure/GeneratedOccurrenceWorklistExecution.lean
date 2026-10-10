import Holant.Proofs.Closure.GeneratedOccurrenceWorklistState

/-! Closed physical preparation of all recursively generated prime-address
resources. The exact current-source batch and its same tagged joint receipts
are stored at every higher event. Termination is multiset arity replacement,
independent of minimum-core sourceOmega; classification remains pending. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklist
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)

inductive Transition : State G base → State G base → Type 1
  | binary (S : State G base) (o : CurrentOccurrences.Id G S.palette) (pending : o ∈ S.todo)
      (ready : OccurrenceWorklist.Ready G S.palette)
      (recomputed : OccurrenceWorklist.inspect G S.palette = .inr ready)
      (arity : weight G S.palette o = 2) : Transition S (S.binary G base o pending)
  | higher (S : State G base) (o : CurrentOccurrences.Id G S.palette) (pending : o ∈ S.todo)
      (ready : OccurrenceWorklist.Ready G S.palette)
      (recomputed : OccurrenceWorklist.inspect G S.palette = .inr ready)
      (input : Input G S.palette o) : Transition S (S.higher G base o pending input ready.torsion)

def Transition.selected {S T : State G base} : Transition G base S T → CurrentOccurrences.Id G S.palette
  | .binary _ o _ _ _ _ => o
  | .higher _ o _ _ _ _ => o

theorem Transition.selected_pending {S T : State G base} (e : Transition G base S T) :
    e.selected G base ∈ S.todo := by cases e <;> assumption

theorem Transition.selected_not_done {S T : State G base} (e : Transition G base S T) :
    e.selected G base ∉ S.done := fun hd => Finset.disjoint_left.mp S.disjoint (e.selected_pending G base) hd

theorem Transition.decreases {S T : State G base} (e : Transition G base S T) : Earlier G base T S := by
  cases e with
  | binary o hp ready hr h2 => exact S.binary_decreases G base o hp
  | higher o hp ready hr b => exact S.higher_decreases G base o hp b ready.torsion

structure BinaryReceipt (P : Palette G) (o : CurrentOccurrences.Id G P) : Type 1 where
  domain : CurrentOccurrences.Domain G P o
  domainIdentity : domain = CurrentOccurrences.domain G P o

def EventWork {S T : State G base} (e : Transition G base S T) : Type 1 := by
  cases e with
  | binary o hp ready hr h2 => exact BinaryReceipt G S.palette o
  | higher o hp ready hr b =>
    exact OccurrenceWorklist.BatchReceipt G S.palette (OccurrenceWorklist.initial G S.palette) o b ready.torsion

def eventWork {S T : State G base} (e : Transition G base S T) : EventWork G base e := by
  cases e with
  | binary o hp ready hr h2 => exact ⟨CurrentOccurrences.domain G S.palette o,rfl⟩
  | higher o hp ready hr b =>
    exact OccurrenceWorklist.batchReceipt G S.palette (OccurrenceWorklist.initial G S.palette) o b ready.torsion

def next (S : State G base) (ready : OccurrenceWorklist.Ready G S.palette)
    (recomputed : OccurrenceWorklist.inspect G S.palette = .inr ready) (nonempty : S.todo.Nonempty) :
    Σ T, Transition G base S T := by
  let o := Classical.choose nonempty
  have pending : o ∈ S.todo := Classical.choose_spec nonempty
  by_cases h2 : weight G S.palette o = 2
  · exact ⟨S.binary G base o pending,.binary S o pending ready recomputed h2⟩
  have h1 := OccurrenceWorklist.ready_nonunary G S.palette (OccurrenceWorklist.initial G S.palette) ready o
  have hpos := CurrentOccurrences.savedLeaf_positive G S.palette o
  have h3 : 3 ≤ weight G S.palette o := by dsimp [weight] at *; omega
  have he : Even (CurrentOccurrences.savedLeaf G S.palette o).1.1 :=
    ready.noOdd _ (CurrentOccurrences.savedLeaf_retained G S.palette o)
      (CurrentOccurrences.savedLeaf_prime G S.palette o) h3
  have h4 : 4 ≤ (CurrentOccurrences.savedLeaf G S.palette o).1.1 := by rcases he with ⟨k,hk⟩; dsimp [weight] at *; omega
  let b := OccurrenceWorklist.batchInput G S.palette (OccurrenceWorklist.initial G S.palette) o h4 he
  exact ⟨S.higher G base o pending b ready.torsion,.higher S o pending ready recomputed b⟩

inductive Trace : State G base → State G base → Type 1
  | nil (S : State G base) : Trace S S
  | cons {S T U : State G base} (event : Transition G base S T) (work : EventWork G base event)
      (rest : Trace T U) : Trace S U

inductive EventIn : {S T : State G base} → Trace G base S T →
    {A B : State G base} → Transition G base A B → Prop
  | head {S T U} (e : Transition G base S T) (w : EventWork G base e) (r : Trace G base T U) :
      EventIn (.cons e w r) e
  | tail {S T U A B} (e : Transition G base S T) (w : EventWork G base e) (r : Trace G base T U)
      (actual : Transition G base A B) (recorded : EventIn r actual) : EventIn (.cons e w r) actual

theorem recorded_work {S T : State G base} (h : Trace G base S T)
    {A B : State G base} (e : Transition G base A B) (he : EventIn G base h e) : Nonempty (EventWork G base e) := by
  induction he with
  | head e w r => exact ⟨w⟩
  | tail e w r actual recorded ih => exact ih

inductive Execution : State G base → Type 1
  | exhausted (S : State G base) (empty : S.todo = ∅) : Execution S
  | structural (S : State G base) (stop : OccurrenceWorklist.Stop G S.palette)
      (recomputed : OccurrenceWorklist.inspect G S.palette = .inl stop) : Execution S
  | next {S T : State G base} (event : Transition G base S T) (work : EventWork G base event)
      (rest : Execution T) : Execution S

def finish (S : State G base) : Execution G base S :=
  (earlier_wellFounded G base).fix (fun S recurse =>
    match hi : OccurrenceWorklist.inspect G S.palette with
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

inductive Outcome (S : State G base) : Type 1
  | exhausted (empty : S.todo = ∅)
  | structural (stop : OccurrenceWorklist.Stop G S.palette)
      (recomputed : OccurrenceWorklist.inspect G S.palette = .inl stop)

def Execution.outcome {S : State G base} (h : Execution G base S) : Outcome G base (h.finalState G base) :=
  match h with
  | .exhausted _ empty => .exhausted empty
  | .structural _ stop inspected => .structural stop inspected
  | .next _ _ rest => rest.outcome

/-- The actual full data execution is retained, not only an erased run proof. -/
structure Result : Type 1 where
  execution : Execution G base (initial G base)

def result : Result G base := ⟨finish G base (initial G base)⟩
def Result.finalState (R : Result G base) := R.execution.finalState G base
def Result.trace (R : Result G base) : Trace G base (initial G base) (R.finalState G base) := R.execution.trace G base
def Result.outcome (R : Result G base) : Outcome G base (R.finalState G base) := R.execution.outcome G base
def Result.frontier (R : Result G base) : CurrentFrontier.Result G (R.finalState G base).palette :=
  CurrentFrontier.build G (R.finalState G base).palette

theorem Result.done_complete (R : Result G base) (empty : (R.finalState G base).todo = ∅) :
    (R.finalState G base).done = Finset.univ := by
  have hp := (R.finalState G base).partition
  simpa only [empty,Finset.empty_union] using hp

theorem Result.current_pending (R : Result G base) (o : CurrentOccurrences.Id G (R.finalState G base).palette) :
    (⟨o,CurrentOccurrences.domain G (R.finalState G base).palette o⟩ :
      (o : CurrentOccurrences.Id G (R.finalState G base).palette) × CurrentOccurrences.Domain G (R.finalState G base).palette o)
        ∈ (R.frontier G base).pending := CurrentFrontier.build_current_coverage G _ o

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklist
