import Holant.Proofs.Closure.TokenExecution

/-! RECONSTRUCTED data-valued exact frozen transitions and finite executions.
The actual producer inspects stored constructors; no progress policy is input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.TokenExecution
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
variable {L : Type*} [Field L] {κ : Type*} [DecidableEq κ] {U : Finset κ}
attribute [local instance] Classical.propDecidable

inductive Transition : FrozenQueue L U → FrozenQueue L U → Type _
  | finish (q : FrozenQueue L U) (k : κ) (pending : k ∈ q.todo) (empty : q.work k = 0) : Transition q (q.finish k)
  | process (q : FrozenQueue L U) (k : κ) (pending : k ∈ q.todo) (W : Multiset (TreeOccurrence L))
      (tree : TreeTransition (q.work k) W) : Transition q (q.process k W)

def Transition.key {q q' : FrozenQueue L U} : Transition q q' → κ
  | .finish _ k _ _ => k
  | .process _ k _ _ _ => k

theorem Transition.key_pending {q q' : FrozenQueue L U} (e : Transition q q') : e.key ∈ q.todo := by
  cases e <;> assumption

def Transition.step {q q' : FrozenQueue L U} (e : Transition q q') : FrozenQueue.Step q' q := by
  cases e with
  | finish k hk hz => exact FrozenQueue.Step.finish _ k hk hz
  | process k hk W tree => exact FrozenQueue.Step.process _ k hk W tree.step

theorem Transition.stored {q q' : FrozenQueue L U} (e : Transition q q')
    (root : κ → TreeOccurrence L) (hq : StoredFrontier root q) : StoredFrontier root q' := by
  cases e with
  | finish k hk hz => exact hq
  | process k hk W tree =>
    intro j t ht
    by_cases he : j = k
    · subst j
      change t ∈ Function.update q.work k W k at ht
      rw [Function.update_self] at ht
      exact treeStep_preserves_stored tree.step (hq k) t ht
    · change t ∈ Function.update q.work k W j at ht
      rw [Function.update_of_ne he] at ht
      exact hq j t ht

def Transition.exposedAt {q q' : FrozenQueue L U} (e : Transition q q') (j : κ) : Multiset (TreeOccurrence L) :=
  match e with
  | .finish _ _ _ _ => 0
  | .process _ k _ _ tree => if j = k then tree.exposed else 0

def Transition.visitedAt {q q' : FrozenQueue L U} (e : Transition q q') (j : κ) : Multiset (TreeOccurrence L) :=
  match e with
  | .finish _ _ _ _ => 0
  | .process _ k _ _ tree => if j = k then tree.visited else 0

inductive Trace : FrozenQueue L U → FrozenQueue L U → Type _
  | nil (q : FrozenQueue L U) : Trace q q
  | cons {q q' q'' : FrozenQueue L U} (event : Transition q q') (rest : Trace q' q'') : Trace q q''

def Trace.runs {q q' : FrozenQueue L U} : Trace q q' → FrozenQueue.Runs q q'
  | .nil _ => .refl
  | .cons e rest => Relation.ReflTransGen.head e.step rest.runs

def Trace.exposed {q q' : FrozenQueue L U} (h : Trace q q') (j : κ) : Multiset (TreeOccurrence L) :=
  match h with
  | .nil _ => 0
  | .cons e rest => e.exposedAt j + rest.exposed j

def Trace.visited {q q' : FrozenQueue L U} (h : Trace q q') (j : κ) : Multiset (TreeOccurrence L) :=
  match h with
  | .nil _ => 0
  | .cons e rest => e.visitedAt j + rest.visited j

theorem Trace.stored {q q' : FrozenQueue L U} (h : Trace q q')
    (root : κ → TreeOccurrence L) (hq : StoredFrontier root q) : StoredFrontier root q' := by
  induction h with
  | nil => exact hq
  | cons e rest ih => exact ih (e.stored root hq)

structure Exhaustion (q : FrozenQueue L U) where
  finalQueue : FrozenQueue L U
  trace : Trace q finalQueue
  exhausted : finalQueue.todo = ∅

def next (q : FrozenQueue L U) (valid : q.Valid) (nonempty : q.todo.Nonempty) : Σ q', Transition q q' := by
  let k := Classical.choose nonempty
  have hk : k ∈ q.todo := Classical.choose_spec nonempty
  by_cases hz : q.work k = 0
  · exact ⟨q.finish k,.finish q k hk hz⟩
  · let t := nextTree (q.work k) (valid k hk) hz
    exact ⟨q.process k t.1,.process q k hk t.1 t.2⟩

def exhaust (q : FrozenQueue L U) (valid : q.Valid) : Exhaustion q :=
  FrozenQueue.step_wellFounded.fix (C := fun q => q.Valid → Exhaustion q) (fun q recurse => fun hv =>
    if hn : q.todo.Nonempty then
      let e := next q hv hn
      let r := recurse e.1 e.2.step (FrozenQueue.step_valid e.2.step hv)
      ⟨r.finalQueue,.cons e.2 r.trace,r.exhausted⟩
    else ⟨q,.nil q,Finset.not_nonempty_iff_eq_empty.mp hn⟩) q valid

def initialExhaustion (root : κ → TreeOccurrence L) : Exhaustion (FrozenQueue.initial U root) :=
  exhaust _ (FrozenQueue.initial_valid U root)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.TokenExecution
