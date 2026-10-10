import Holant.Proofs.Closure.QueueJoint
import Holant.Proofs.Closure.HistoryCatalogue

/-! Exact physical receipts for the ambient-key trace actually used in the
all-arity history. Pending keys are decoded from the frozen image catalogue;
there is no assertion that a separately chosen native-key queue has the same
schedule. Every receipt is indexed by the actual ambient event. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.AmbientQueue
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
open Holant.LocalDrafts.Hardness.GeneralExtraction
open TokenExecution
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature Holant.Tractable.AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))

abbrev Key := HistoryCatalogue.Key (OI.K G)
abbrev Universe := HistoryCatalogue.keyUniverse P.family torsion f
abbrev Root := HistoryCatalogue.root P.family torsion f
abbrev Queue := FrozenQueue (OI.K G) (Universe G P torsion f)

/-- Decode only an actual key of this frozen catalogue. -/
def decode (j : Key G) (hj : j ∈ Universe G P torsion f) :
    FullDeckIndex P.family torsion f := Classical.choose (Finset.mem_image.mp hj)

theorem decode_binding (j : Key G) (hj : j ∈ Universe G P torsion f) :
    HistoryCatalogue.embed P.family torsion f (decode G P torsion f j hj) = j :=
  (Classical.choose_spec (Finset.mem_image.mp hj)).2

theorem root_binding (j : Key G) (hj : j ∈ Universe G P torsion f) :
    Root G P torsion f j = fullDeckRoot P.family torsion f (decode G P torsion f j hj) :=
  (congrArg (Root G P torsion f) (decode_binding G P torsion f j hj)).symm.trans
    (HistoryCatalogue.root_binding P.family torsion f (decode G P torsion f j hj))

/-- Physical resource and explicit key-decoding receipts for the SAME ambient
inspection, including both open split children and immediately exposed leaves. -/
structure ProcessPhysical (q : Queue G P torsion f)
    (j : Key G) (W : Multiset (TreeOccurrence (OI.K G)))
    (e : TreeTransition (q.work j) W) where
  nativeKey : FullDeckIndex P.family torsion f
  keyIdentity : HistoryCatalogue.embed P.family torsion f nativeKey = j
  rootIdentity : Root G P torsion f j = fullDeckRoot P.family torsion f nativeKey
  stored : StoredSubtree e.focus (fullDeckRoot P.family torsion f nativeKey)
  access : GeneralPowerExposure.PowerMacro P.table e.focus.1.2
  toOriginal : RetainedBranch.ToOriginalProgramme G P e.focus.1
  toOriginalIdentity : toOriginal = RetainedBranch.toOriginal G P e.focus.1 access
  fromOriginal : RetainedBranch.FromOriginalProgramme G P e.focus.1
  fromOriginalIdentity : fromOriginal = RetainedBranch.fromOriginal G P e.focus.1
  savedRoot : RetainedCatalogue.occurrence G P torsion f
    (RetainedCatalogue.deckLabel G P torsion f nativeKey) = fullDeckRoot P.family torsion f nativeKey
  descendantsRetained : ∀ g ∈ e.focus.2.leaves, g ∈ RetainedCatalogue.family G P torsion f
  exposedSaved : ∀ u ∈ e.exposed, ∃ i : Fin (RetainedCatalogue.count G P torsion f),
    RetainedCatalogue.occurrence G P torsion f i = u
  childrenAccess : ∀ u ∈ FullQueue.immediateChildren e, GeneralPowerExposure.PowerMacro P.table u.1.2
  childrenToOriginal : ∀ u ∈ FullQueue.immediateChildren e, RetainedBranch.ToOriginalProgramme G P u.1
  childrenToOriginalIdentity : ∀ u hu, childrenToOriginal u hu =
    RetainedBranch.toOriginal G P u.1 (childrenAccess u hu)
  exposedAccess : ∀ u ∈ e.exposed, GeneralPowerExposure.PowerMacro P.table u.1.2
  exposedToOriginal : ∀ u ∈ e.exposed, RetainedBranch.ToOriginalProgramme G P u.1
  exposedToOriginalIdentity : ∀ u hu, exposedToOriginal u hu =
    RetainedBranch.toOriginal G P u.1 (exposedAccess u hu)

variable (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)

def processPhysical (q : Queue G P torsion f) (hq : StoredFrontier (Root G P torsion f) q)
    (j : Key G) (hj : j ∈ q.todo) (W : Multiset (TreeOccurrence (OI.K G)))
    (e : TreeTransition (q.work j) W) : ProcessPhysical G P torsion f q j W e := by
  let k := decode G P torsion f j (q.within hj)
  have hr := root_binding G P torsion f j (q.within hj)
  have hs : StoredSubtree e.focus (fullDeckRoot P.family torsion f k) := by
    rw [← hr]
    exact hq j e.focus e.focus_mem
  let M := FullQueue.storedAccess G P torsion f core hcore k e.focus hs
  let children := fun u hu => FullQueue.storedAccess G P torsion f core hcore k u
    (FullQueue.stored_trans (FullQueue.immediateChildren_stored e u hu) hs)
  let exposed := fun u hu => FullQueue.storedAccess G P torsion f core hcore k u
    (FullQueue.stored_trans (e.exposed_stored u hu) hs)
  refine ⟨k,decode_binding G P torsion f j (q.within hj),hr,hs,M,
    RetainedBranch.toOriginal G P e.focus.1 M,rfl,RetainedBranch.fromOriginal G P e.focus.1,rfl,
    RetainedCatalogue.deck_saved G P torsion f k,?_,?_,children,
    (fun u hu => RetainedBranch.toOriginal G P u.1 (children u hu)),fun _ _ => rfl,
    exposed,(fun u hu => RetainedBranch.toOriginal G P u.1 (exposed u hu)),fun _ _ => rfl⟩
  · intro g hg
    rw [RetainedCatalogue.family_exact]
    exact fullRetainedDeck_leaf P.family torsion f k g
      (Holant.LocalDrafts.Hardness.FactorSaturation.stored_leaves_subset hs g hg)
  · intro u hu
    exact RetainedCatalogue.leaf_occurrence_saved G P torsion f k u
      (FullQueue.stored_leaf_subset hs u (FullQueue.exposed_leaf_subset e u hu))

def EventPhysical {q q' : Queue G P torsion f} (e : Transition q q') : Type 1 :=
by
  cases e with
  | finish j hj hz => exact PUnit.{2}
  | process j hj W ht => exact ProcessPhysical G P torsion f q j W ht

def eventPhysical {q q' : Queue G P torsion f} (e : Transition q q')
    (hq : StoredFrontier (Root G P torsion f) q) : EventPhysical G P torsion f e := by
  cases e with
  | finish j hj hz => exact PUnit.unit
  | process j hj W ht => exact processPhysical G P torsion f core hcore q hq j hj W ht

variable (hm : 2 ≤ m)

structure JointEvent (first : Bool) {q q' : Queue G P torsion f} (e : Transition q q') where
  before : Palette G
  after : Palette G
  beforeIdentity : before = FullQueue.beforePalette G P torsion f core hcore hm first
  afterIdentity : after = FullQueue.augmentedPalette G P torsion f core hcore hm
  retains : before.family ⊆ after.family
  oldSaved : ∀ i : Fin before.count, ∃ j : Fin after.count,
    (⟨⟨after.arity j.val,after.table j⟩,after.trees j⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨before.arity i.val,before.table i⟩,before.trees i⟩
  keyPending : e.key ∈ q.todo
  exactTransition : FrozenQueue.Step q' q
  physical : EventPhysical G P torsion f e
  toOriginalMachine : after.toOriginal.controlled.reduction.machine =
    (ProgrammeRetained.controlledToOriginal G P torsion f core hcore).reduction.machine
  fromOriginalMachine : after.fromOriginal.controlled.reduction.machine =
    (ProgrammeRetained.controlledFromOriginal G P torsion f).reduction.machine

def jointEvent (first : Bool) {q q' : Queue G P torsion f} (e : Transition q q')
    (hq : StoredFrontier (Root G P torsion f) q) :
    JointEvent G P torsion f core hcore hm first e := by
  refine ⟨FullQueue.beforePalette G P torsion f core hcore hm first,
    FullQueue.augmentedPalette G P torsion f core hcore hm,rfl,rfl,?_,?_,e.key_pending,e.step,
    eventPhysical G P torsion f core hcore e hq,rfl,rfl⟩
  · cases first with
    | false => exact fun _ h => h
    | true =>
        change P.family ⊆ (ProgrammeRetained.palette G P torsion f core hcore hm).family
        rw [ProgrammeRetained.palette_family]
        exact fullRetainedDeck_retains P.family torsion f
  · cases first with
    | false => exact fun i => ⟨i,rfl⟩
    | true => exact fun i => ⟨RetainedCatalogue.oldLabel G P torsion f i,
        RetainedCatalogue.old_saved G P torsion f i⟩

def JointTrace (first : Bool) {q q' : Queue G P torsion f} (h : Trace q q') : Type 1 :=
  match h with
  | .nil _ => PUnit.{2}
  | .cons e rest => JointEvent G P torsion f core hcore hm first e ×
      JointTrace false rest

def jointTrace (first : Bool) {q q' : Queue G P torsion f} (h : Trace q q')
    (hq : StoredFrontier (Root G P torsion f) q) :
    JointTrace G P torsion f core hcore hm first h :=
  match h with
  | .nil _ => PUnit.unit
  | .cons e rest => (jointEvent G P torsion f core hcore hm first e hq,
      jointTrace false rest (e.stored _ hq))

/-- Receipts for the SAME ambient trace stored by all-arity mathematical history. -/
def savedJoint : JointTrace G P torsion f core hcore hm true
    (HistoryCatalogue.exhaust P.family torsion f).trace :=
  jointTrace G P torsion f core hcore hm true (HistoryCatalogue.exhaust P.family torsion f).trace
    (initial_stored _)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.AmbientQueue
end
