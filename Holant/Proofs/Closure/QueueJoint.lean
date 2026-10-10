import Holant.Proofs.Closure.QueueBatch
import Holant.Proofs.Closure.RetainedSingle

/-! RECONSTRUCTED from the retained earlier QueueJoint seed and exact
accepted later ambient/tagged wrappers. Requires fresh strict validation.

Joint, event-indexed palette/tree/programme receipts. The full retained
augmentation is installed by the first real queue transition; later steps keep
that exact palette. Every inspected subtree and exposed child has a separate
physically composed original-G programme, explicitly charging intermediate
composite access without pretending it is a final retained alphabet label. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.FullQueue
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
open Holant.LocalDrafts.Hardness
open TokenExecution
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature Holant.Tractable.AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))

theorem exposed_leaf_subset {L : Type*} [Field L]
    {V W : Multiset (TreeOccurrence L)} (e : TreeTransition V W) :
    ∀ t ∈ e.exposed, t ∈ leafOccurrences e.focus.2 := by
  cases e with
  | leaf f hp hn rest => exact fun _ ht => ht
  | split sp ta tb rest =>
      intro t ht
      rcases Multiset.mem_add.mp ht with ha | hb
      · apply Multiset.mem_add.mpr
        left
        unfold closedLeaves at ha
        split_ifs at ha with hn
        · simp at ha
        · exact ha
      · apply Multiset.mem_add.mpr
        right
        unfold closedLeaves at hb
        split_ifs at hb with hn
        · simp at hb
        · exact hb

theorem stored_leaf_subset {L : Type*} [Field L]
    {u t : TreeOccurrence L} (h : StoredSubtree u t) :
    ∀ v ∈ leafOccurrences u.2, v ∈ leafOccurrences t.2 := by
  induction h with
  | root => exact fun _ hv => hv
  | left sp ta tb h ih => exact fun v hv => Multiset.mem_add.mpr (Or.inl (ih v hv))
  | right sp ta tb h ih => exact fun v hv => Multiset.mem_add.mpr (Or.inr (ih v hv))

/-- Both genuine split children, including children that remain open. -/
def immediateChildren {L : Type*} [Field L]
    {V W : Multiset (TreeOccurrence L)} (e : TreeTransition V W) : Multiset (TreeOccurrence L) :=
  match e with
  | .leaf _ _ _ _ => 0
  | .split _ ta tb _ => {⟨_,ta⟩} + {⟨_,tb⟩}

theorem immediateChildren_stored {L : Type*} [Field L]
    {V W : Multiset (TreeOccurrence L)} (e : TreeTransition V W) :
    ∀ u ∈ immediateChildren e, StoredSubtree u e.focus := by
  cases e with
  | leaf => simp [immediateChildren]
  | split sp ta tb rest =>
      intro u hu
      rcases Multiset.mem_add.mp hu with ha | hb
      · have he := Multiset.mem_singleton.mp ha
        subst u
        exact .left sp ta tb (.root _)
      · have he := Multiset.mem_singleton.mp hb
        subst u
        exact .right sp ta tb (.root _)

theorem stored_trans {L : Type*} [Field L] {u v w : TreeOccurrence L}
    (huv : StoredSubtree u v) (hvw : StoredSubtree v w) : StoredSubtree u w := by
  induction hvw with
  | root => exact huv
  | left sp ta tb h ih => exact .left sp ta tb (ih huv)
  | right sp ta tb h ih => exact .right sp ta tb (ih huv)

/-- This receipt is indexed by the exact key, exact before frontier and exact
stored transition. Its physical programme uses the SAME constructed network. -/
structure ProcessPhysical (q : Queue G P torsion f)
    (k : Key G P torsion f) (W : Multiset (TreeOccurrence (OI.K G)))
    (e : TreeTransition (q.work k) W) where
  networks : ProcessNetworks G P torsion f q k W e
  toOriginal : RetainedBranch.ToOriginalProgramme G P e.focus.1
  toOriginalIdentity : toOriginal = RetainedBranch.toOriginal G P e.focus.1 networks.access
  fromOriginal : RetainedBranch.FromOriginalProgramme G P e.focus.1
  fromOriginalIdentity : fromOriginal = RetainedBranch.fromOriginal G P e.focus.1
  exposedSaved : ∀ u ∈ e.exposed, ∃ j : Fin (RetainedCatalogue.count G P torsion f),
    RetainedCatalogue.occurrence G P torsion f j = u
  exposedToOriginal : ∀ u ∈ e.exposed, RetainedBranch.ToOriginalProgramme G P u.1
  exposedToOriginalIdentity : ∀ u hu, exposedToOriginal u hu =
    RetainedBranch.toOriginal G P u.1 (networks.exposedAccess u hu)
  childrenAccess : ∀ u ∈ immediateChildren e,
    Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralPowerExposure.PowerMacro P.table u.1.2
  childrenToOriginal : ∀ u ∈ immediateChildren e, RetainedBranch.ToOriginalProgramme G P u.1
  childrenToOriginalIdentity : ∀ u hu, childrenToOriginal u hu =
    RetainedBranch.toOriginal G P u.1 (childrenAccess u hu)

/-- No branch programme or coverage policy is supplied: both the graph and
its controlled original-G machine are constructed for this actual inspection. -/
def processPhysical (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (q : Queue G P torsion f) (hq : StoredFrontier (Root G P torsion f) q)
    (k : Key G P torsion f) (W : Multiset (TreeOccurrence (OI.K G)))
    (e : TreeTransition (q.work k) W) : ProcessPhysical G P torsion f q k W e := by
  let N := processNetworks G P torsion f core hcore q hq k W e
  let children := fun u hu => storedAccess G P torsion f core hcore k u
    (stored_trans (immediateChildren_stored e u hu) N.stored)
  refine ⟨N,RetainedBranch.toOriginal G P e.focus.1 N.access,rfl,
    RetainedBranch.fromOriginal G P e.focus.1,rfl,?_,
    (fun u hu => RetainedBranch.toOriginal G P u.1 (N.exposedAccess u hu)),fun _ _ => rfl,
    children,(fun u hu => RetainedBranch.toOriginal G P u.1 (children u hu)),fun _ _ => rfl⟩
  intro u hu
  exact RetainedCatalogue.leaf_occurrence_saved G P torsion f k u
    (stored_leaf_subset N.stored u (exposed_leaf_subset e u hu))

def EventPhysical {q q' : Queue G P torsion f} (e : Transition q q') : Type 1 := by
  cases e with
  | finish k hk hz => exact PUnit.{2}
  | process k hk W ht => exact ProcessPhysical G P torsion f q k W ht

def eventPhysical (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    {q q' : Queue G P torsion f} (e : Transition q q')
    (hq : StoredFrontier (Root G P torsion f) q) : EventPhysical G P torsion f e := by
  cases e with
  | finish k hk hz => exact PUnit.unit
  | process k hk W ht => exact processPhysical G P torsion f core hcore q hq k W ht

variable (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩) (hm : 2 ≤ m)

def augmentedPalette : Palette G := ProgrammeRetained.palette G P torsion f core hcore hm

def beforePalette (first : Bool) : Palette G :=
  if first then P else augmentedPalette G P torsion f core hcore hm

/-- Explicit before/after physical palette identities, together with the
same event's tree/network/programme receipt. The first actual queue event
installs the complete catalogue; subsequent events keep that exact palette. -/
structure JointEvent (first : Bool) {q q' : Queue G P torsion f} (e : Transition q q') where
  before : Palette G
  after : Palette G
  beforeIdentity : before = beforePalette G P torsion f core hcore hm first
  afterIdentity : after = augmentedPalette G P torsion f core hcore hm
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
  refine ⟨beforePalette G P torsion f core hcore hm first,
    augmentedPalette G P torsion f core hcore hm,rfl,rfl,?_,?_,e.key_pending,e.step,
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

/-- The receipt list's exact Trace is a type index, preventing substitution of
an unrelated exhaustion run. Palette states match across consecutive events. -/
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

/-- Closed joint receipt producer for the actual complete batch's trace. -/
def savedJoint : JointTrace G P torsion f core hcore hm true
    (execution G P torsion f).trace :=
  jointTrace G P torsion f core hcore hm true (execution G P torsion f).trace
    (initial_stored _)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.FullQueue
end
