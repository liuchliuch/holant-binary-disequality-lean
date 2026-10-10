import Holant.Proofs.Closure.GeneratedGroupWorklistState

/-! Closed lexicographic original-field group-deficit / pending-arity producer.
Every strict actual-group growth restarts the exact current addressed universe;
every unchanged-group step retains its real physical preparation event.
No sourceOmega-switch, local rigidity or later two-copy closure is asserted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupWorklist
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)

inductive Trace : Active G base → Active G base → Type 1
  | nil (S : Active G base) : Trace S S
  | cons {S T U : Active G base} (event : Transition G base S T) (rest : Trace T U) : Trace S U

structure Stopped (S : Active G base) : Type 1 where
  last : Active G base
  trace : Trace G base S last
  finalSource : Source G base
  terminal : GeneratedOccurrenceWorklist.Transition G base last.source finalSource
  work : GeneratedOccurrenceWorklist.EventWork G base terminal
  stop : OccurrenceWorklist.Stop G finalSource.palette
  recomputed : OccurrenceWorklist.inspect G finalSource.palette = .inl stop

structure Exhausted (S : Active G base) : Type 1 where
  final : Active G base
  trace : Trace G base S final
  empty : final.source.todo = ∅

abbrev Completion (S : Active G base) := Stopped G base S ⊕ Exhausted G base S

def Stopped.prepend {S T : Active G base} (e : Transition G base S T) (r : Stopped G base T) : Stopped G base S :=
  ⟨r.last,.cons e r.trace,r.finalSource,r.terminal,r.work,r.stop,r.recomputed⟩

def Exhausted.prepend {S T : Active G base} (e : Transition G base S T) (r : Exhausted G base T) : Exhausted G base S :=
  ⟨r.final,.cons e r.trace,r.empty⟩

def prepend {S T : Active G base} (e : Transition G base S T) : Completion G base T → Completion G base S
  | .inl stopped => .inl (stopped.prepend G base e)
  | .inr exhausted => .inr (exhausted.prepend G base e)

def finish (S : Active G base) : Completion G base S :=
  (earlier_wellFounded G base).fix (fun S recurse =>
    match dispatch G base S with
    | .exhausted empty => .inr ⟨S,.nil S,empty⟩
    | .structural raw event work stop inspected => .inl ⟨S,.nil S,raw,event,work,stop,inspected⟩
    | .next T event => prepend G base event (recurse T (event.decreases G base))) S

/-- Initial structural exits require no fake residual certificate. Otherwise
all future programmes/worklists and strict group restarts are built internally. -/
inductive Result : Type 1
  | initialStop (stop : OccurrenceWorklist.Stop G base)
      (recomputed : OccurrenceWorklist.inspect G base = .inl stop)
  | prepared (ready : OccurrenceWorklist.Ready G base)
      (recomputed : OccurrenceWorklist.inspect G base = .inr ready)
      (completion : Completion G base ⟨GeneratedOccurrenceWorklist.initial G base,ready,recomputed⟩)

def result : Result G base :=
  match hi : OccurrenceWorklist.inspect G base with
  | .inl stop => .initialStop stop hi
  | .inr ready => .prepared ready hi (finish G base ⟨GeneratedOccurrenceWorklist.initial G base,ready,hi⟩)

def Result.finalSource : Result G base → Source G base
  | .initialStop _ _ => GeneratedOccurrenceWorklist.initial G base
  | .prepared _ _ (.inl stopped) => stopped.finalSource
  | .prepared _ _ (.inr exhausted) => exhausted.final.source

def Result.frontier (R : Result G base) : CurrentFrontier.Result G (R.finalSource G base).palette :=
  CurrentFrontier.build G (R.finalSource G base).palette

inductive Outcome (S : Source G base) : Type 1
  | structural (stop : OccurrenceWorklist.Stop G S.palette)
      (recomputed : OccurrenceWorklist.inspect G S.palette = .inl stop)
  | exhausted (ready : OccurrenceWorklist.Ready G S.palette)
      (recomputed : OccurrenceWorklist.inspect G S.palette = .inr ready)
      (empty : S.todo = ∅)

def Result.outcome (R : Result G base) : Outcome G base (R.finalSource G base) :=
  match R with
  | .initialStop stop recomputed => .structural stop recomputed
  | .prepared _ _ (.inl stopped) => .structural stopped.stop stopped.recomputed
  | .prepared _ _ (.inr exhausted) => .exhausted exhausted.final.ready exhausted.final.recomputed exhausted.empty

theorem Exhausted.done_complete {S : Active G base} (r : Exhausted G base S) : r.final.source.done = Finset.univ := by
  simpa only [r.empty,Finset.empty_union] using r.final.source.partition

theorem Result.current_pending (R : Result G base) (q : CurrentOccurrences.Id G (R.finalSource G base).palette) :
    (⟨q,CurrentOccurrences.domain G (R.finalSource G base).palette q⟩ :
      (q : CurrentOccurrences.Id G (R.finalSource G base).palette) × CurrentOccurrences.Domain G (R.finalSource G base).palette q)
        ∈ (R.frontier G base).pending := CurrentFrontier.build_current_coverage G _ q

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupWorklist
