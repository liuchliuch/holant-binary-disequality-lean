import Holant.Proofs.Closure.QueueDeckKernel
import Holant.Proofs.Closure.RetainedCatalogue

/-! RECONSTRUCTED full literal-deck queue. All coverage and access refer to
this one addressed constructor execution and the once-saved root trees. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.FullQueue
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction
open TokenExecution
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
attribute [local instance] Classical.propDecidable

abbrev Key := DeckExecution.Key P.family torsion f
abbrev Universe := DeckExecution.Universe P.family torsion f
abbrev Root := DeckExecution.Root P.family torsion f
abbrev Queue := FrozenQueue (OI.K G) (Universe G P torsion f)

def taggedExecution := DeckExecution.taggedExecution P.family torsion f
def execution := DeckExecution.execution P.family torsion f
def finalQueue : Queue G P torsion f := DeckExecution.finalQueue P.family torsion f

theorem initial_to_final : FrozenQueue.Runs
    (FrozenQueue.initial (Universe G P torsion f) (Root G P torsion f)) (finalQueue G P torsion f) :=
  DeckExecution.initial_to_final P.family torsion f

theorem exhausted : (finalQueue G P torsion f).todo = ∅ := DeckExecution.exhausted P.family torsion f

theorem allDone : (finalQueue G P torsion f).done = Universe G P torsion f :=
  DeckExecution.allDone P.family torsion f

theorem leaves_covered (k : Key G P torsion f) :
    (QueueTagged.initialExposed (U:=Universe G P torsion f) (Root G P torsion f) k).map Prod.snd =
      leafOccurrences (Root G P torsion f k).2 :=
  DeckExecution.leaves_covered P.family torsion f k

theorem nodes_covered (k : Key G P torsion f) :
    (QueueTagged.initialVisited (U:=Universe G P torsion f) (Root G P torsion f) k).map Prod.snd =
      nodeOccurrences (Root G P torsion f k).2 :=
  DeckExecution.nodes_covered P.family torsion f k

theorem same_trace_leaf_projection (k : Key G P torsion f) :
    (QueueTagged.initialExposed (U:=Universe G P torsion f) (Root G P torsion f) k).map Prod.snd =
      closedLeaves (Root G P torsion f k) + (execution G P torsion f).trace.exposed k :=
  DeckExecution.same_trace_leaf_projection P.family torsion f k

theorem same_trace_node_projection (k : Key G P torsion f) :
    (QueueTagged.initialVisited (U:=Universe G P torsion f) (Root G P torsion f) k).map Prod.snd =
      closedNodes (Root G P torsion f k) + (execution G P torsion f).trace.visited k :=
  DeckExecution.same_trace_node_projection P.family torsion f k

theorem root_open (hm : 2 ≤ m) (k : Key G P torsion f) : 2 ≤ (Root G P torsion f k).1.1 :=
  DeckExecution.root_open P.family torsion f hm k

theorem initial_closed_zero (hm : 2 ≤ m) (k : Key G P torsion f) :
    closedLeaves (Root G P torsion f k) = 0 ∧ closedNodes (Root G P torsion f k) = 0 :=
  DeckExecution.initial_closed_zero P.family torsion f hm k

theorem initial_event_inspects (hm : 2 ≤ m) {q : Queue G P torsion f}
    (e : Transition (FrozenQueue.initial (Universe G P torsion f) (Root G P torsion f)) q) :
    ∃ (k : Key G P torsion f) (W : Multiset (TreeOccurrence (OI.K G))),
      Nonempty (TreeTransition (openTree (Root G P torsion f k)) W) :=
  DeckExecution.initial_event_inspects P.family torsion f hm e

theorem execution_nonempty : ∃ (q q' : Queue G P torsion f) (e : Transition q q'),
    q = FrozenQueue.initial (Universe G P torsion f) (Root G P torsion f) :=
  DeckExecution.execution_nonempty P.family torsion f

private theorem subtree_trans {L : Type*} [Field L] {u v w : TreeOccurrence L}
    (huv : StoredSubtree u v) (hvw : StoredSubtree v w) : StoredSubtree u w := by
  induction hvw with
  | root => exact huv
  | left sp l r h ih => exact .left sp l r (ih huv)
  | right sp l r h ih => exact .right sp l r (ih huv)

variable (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)

def storedAccess (k : Key G P torsion f) (u : TreeOccurrence (OI.K G))
    (hu : StoredSubtree u (Root G P torsion f k)) : GeneralPowerExposure.PowerMacro P.table u.1.2 :=
  deckSubtreePower G P torsion f core hcore k u hu

/-- This data is indexed by the actual key, actual pending frontier and exact
constructor transition. Intermediate composites get charged branch access. -/
structure ProcessNetworks (q : Queue G P torsion f) (k : Key G P torsion f)
    (W : Multiset (TreeOccurrence (OI.K G))) (e : TreeTransition (q.work k) W) where
  stored : StoredSubtree e.focus (Root G P torsion f k)
  access : GeneralPowerExposure.PowerMacro P.table e.focus.1.2
  savedRoot : RetainedCatalogue.occurrence G P torsion f
    (RetainedCatalogue.deckLabel G P torsion f k) = Root G P torsion f k
  descendantsRetained : ∀ g ∈ e.focus.2.leaves, g ∈ RetainedCatalogue.family G P torsion f
  exposedAccess : ∀ u ∈ e.exposed, GeneralPowerExposure.PowerMacro P.table u.1.2

def processNetworks (q : Queue G P torsion f) (hq : StoredFrontier (Root G P torsion f) q)
    (k : Key G P torsion f) (W : Multiset (TreeOccurrence (OI.K G)))
    (e : TreeTransition (q.work k) W) : ProcessNetworks G P torsion f q k W e := by
  let hs := hq k e.focus e.focus_mem
  refine ⟨hs,storedAccess G P torsion f core hcore k e.focus hs,
    RetainedCatalogue.deck_saved G P torsion f k,?_,
    (fun u hu => storedAccess G P torsion f core hcore k u (subtree_trans (e.exposed_stored u hu) hs))⟩
  intro g hg
  rw [RetainedCatalogue.family_exact]
  exact fullRetainedDeck_leaf P.family torsion f k g (FactorSaturation.stored_leaves_subset hs g hg)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.FullQueue
