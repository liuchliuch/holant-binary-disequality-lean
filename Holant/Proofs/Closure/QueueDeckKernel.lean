import Holant.Proofs.Closure.QueueTagged
import Holant.Proofs.FiniteGroups.Stabilization.FullRetainedDeck

/-! RECONSTRUCTED literal complete-deck execution kernel. Every resource and
first-event witness uses the same actual full-key addressed producer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.DeckExecution
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
open TokenExecution
variable {L : Type} [Field L] [NumberField L]
variable (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable {m : ℕ} (f : Signature L (m+2))
attribute [local instance] Classical.propDecidable

abbrev Key := FullDeckIndex F torsion f
abbrev Universe := fullDeckUniverse F torsion f
abbrev Root := fullDeckRoot F torsion f
abbrev Queue := FrozenQueue L (Universe F torsion f)

def taggedExecution := QueueTagged.initialExhaustion (U:=Universe F torsion f) (Root F torsion f)
def execution := QueueTagged.projectedExhaustion (U:=Universe F torsion f) (Root F torsion f)
def finalQueue : Queue F torsion f := (execution F torsion f).finalQueue

theorem initial_to_final : FrozenQueue.Runs
    (FrozenQueue.initial (Universe F torsion f) (Root F torsion f)) (finalQueue F torsion f) :=
  (execution F torsion f).trace.runs

theorem exhausted : (finalQueue F torsion f).todo = ∅ := (execution F torsion f).exhausted

theorem allDone : (finalQueue F torsion f).done = Universe F torsion f :=
  FrozenQueue.done_eq_universe_of_exhausted _ (exhausted F torsion f)

theorem leaves_covered (k : Key F torsion f) :
    (QueueTagged.initialExposed (U:=Universe F torsion f) (Root F torsion f) k).map Prod.snd =
      leafOccurrences (Root F torsion f k).2 := by
  rw [QueueTagged.initial_leaf_addresses _ _ (mem_fullDeckUniverse _ _ _ k),QueueTagged.treeLeaves_project]

theorem nodes_covered (k : Key F torsion f) :
    (QueueTagged.initialVisited (U:=Universe F torsion f) (Root F torsion f) k).map Prod.snd =
      nodeOccurrences (Root F torsion f k).2 := by
  rw [QueueTagged.initial_node_addresses _ _ (mem_fullDeckUniverse _ _ _ k),QueueTagged.treeNodes_project]

theorem same_trace_leaf_projection (k : Key F torsion f) :
    (QueueTagged.initialExposed (U:=Universe F torsion f) (Root F torsion f) k).map Prod.snd =
      closedLeaves (Root F torsion f k) + (execution F torsion f).trace.exposed k :=
  QueueTagged.initialExposed_project _ _

theorem same_trace_node_projection (k : Key F torsion f) :
    (QueueTagged.initialVisited (U:=Universe F torsion f) (Root F torsion f) k).map Prod.snd =
      closedNodes (Root F torsion f k) + (execution F torsion f).trace.visited k :=
  QueueTagged.initialVisited_project _ _

theorem root_open (hm : 2 ≤ m) (k : Key F torsion f) : 2 ≤ (Root F torsion f k).1.1 := by
  cases k with
  | inl q => exact Nat.le_refl 2
  | inr k => exact hm

theorem initial_closed_zero (hm : 2 ≤ m) (k : Key F torsion f) :
    closedLeaves (Root F torsion f k) = 0 ∧ closedNodes (Root F torsion f k) = 0 := by
  simp [closedLeaves,closedNodes,root_open F torsion f hm k]

/-- Every actual first transition inspects a nonempty proper root, never an
empty-work shortcut. -/
theorem initial_event_inspects (hm : 2 ≤ m) {q : Queue F torsion f}
    (e : Transition (FrozenQueue.initial (Universe F torsion f) (Root F torsion f)) q) :
    ∃ (k : Key F torsion f) (W : Multiset (TreeOccurrence L)),
      Nonempty (TreeTransition (openTree (Root F torsion f k)) W) := by
  cases e with
  | finish k hk hz =>
    have hn := root_open F torsion f hm k
    simp [FrozenQueue.initial,openTree,hn] at hz
  | process k hk W tree => exact ⟨k,W,⟨tree⟩⟩

/-- Nonempty literal universe means the returned trace has an actual event. -/
theorem execution_nonempty : ∃ (q q' : Queue F torsion f) (e : Transition q q'),
    q = FrozenQueue.initial (Universe F torsion f) (Root F torsion f) := by
  have hn : (Universe F torsion f).Nonempty :=
    ⟨.inl 1,mem_fullDeckUniverse _ _ _ (.inl 1)⟩
  have first {q q' : Queue F torsion f} (h : Trace q q') (hs : q.todo.Nonempty)
      (he : q'.todo = ∅) : ∃ q'', Nonempty (Transition q q'') := by
    cases h with
    | nil q => exact (Finset.not_nonempty_empty (he ▸ hs)).elim
    | cons e rest => exact ⟨_,⟨e⟩⟩
  obtain ⟨q',⟨e⟩⟩ := first (execution F torsion f).trace hn (execution F torsion f).exhausted
  exact ⟨_,q',e,rfl⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.DeckExecution
