import Holant.Proofs.Closure.OccurrenceBatch
import Holant.Proofs.Closure.DeckLocation
import Holant.Proofs.Closure.RetainedSingle

/-! Joint exact-address receipts for retained, possibly nonminimum occurrences.
Every programme is constructed from the same saved slot and is physically charged
at its explicit P+branch boundary. The returned palette is OccurrenceBatch.palette,
and the tagged run projects to precisely OccurrenceBatch.result's frozen run. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceBatchJoint
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (retained : (⟨m+2,f⟩ : AnySignature (OI.K G)) ∈ P.family)

abbrev Key := FullQueue.Key G P torsion f
abbrev Root := FullQueue.Root G P torsion f
abbrev TaggedState := QueueTagged.State (U:=FullQueue.Universe G P torsion f) (Root G P torsion f)

def addressPower (k : Key G P torsion f) (u : QueueTagged.Item (OI.K G))
    (h : QueueTagged.lookupTree (Root G P torsion f k) u.1 = some u.2) :
    GeneralPowerExposure.PowerMacro P.table u.2.1.2 :=
  DeckAddressAccess.locatedData (Root G P torsion f k) u.1 u.2 h
    (fun v => GeneralPowerExposure.PowerMacro P.table v.1.2)
    (OccurrenceBatch.slotPower G P torsion f retained k)

theorem addressPower_at_slot (k : Key G P torsion f)
    (j : FactorSaturation.Slots (Root G P torsion f k).2) :
    addressPower G P torsion f retained k
      (FactorSaturation.path (Root G P torsion f k).2 j,FactorSaturation.slot (Root G P torsion f k).2 j)
      (DeckAddressAccess.lookupTree_slot (Root G P torsion f k).2 j) =
        OccurrenceBatch.slotPower G P torsion f retained k j :=
  DeckAddressAccess.locatedData_at_slot (Root G P torsion f k).2 j
    (fun v => GeneralPowerExposure.PowerMacro P.table v.1.2)
    (OccurrenceBatch.slotPower G P torsion f retained k)

/-- The same canonical leaf macro is installed in this occurrence batch. -/
theorem addressPower_installed_leaf (k : Key G P torsion f)
    (j : FactorSaturation.Leaves (Root G P torsion f k).2) :
    addressPower G P torsion f retained k
      (FactorSaturation.path (Root G P torsion f k).2 (FactorSaturation.leafSlot _ j),
        FactorSaturation.slot (Root G P torsion f k).2 (FactorSaturation.leafSlot _ j))
      (DeckAddressAccess.lookupTree_slot (Root G P torsion f k).2 (FactorSaturation.leafSlot _ j)) =
        OccurrenceBatch.indexPower G P torsion f retained (.inr ⟨k,j⟩) :=
  addressPower_at_slot G P torsion f retained k _

/-- The full data pair records the actual slot even through dependent casts. -/
theorem addressPower_pair (k : Key G P torsion f) (u : QueueTagged.Item (OI.K G))
    (h : QueueTagged.lookupTree (Root G P torsion f k) u.1 = some u.2) :
    (⟨u.2,addressPower G P torsion f retained k u h⟩ :
      Σ v : TreeOccurrence (OI.K G), GeneralPowerExposure.PowerMacro P.table v.1.2) =
    ⟨FactorSaturation.slot (Root G P torsion f k).2
      (DeckAddressAccess.locatedSlot (Root G P torsion f k) u.1 u.2 h),
      OccurrenceBatch.slotPower G P torsion f retained k
        (DeckAddressAccess.locatedSlot (Root G P torsion f k) u.1 u.2 h)⟩ :=
  DeckAddressAccess.transport_data_pair
    (DeckAddressAccess.locatedSlot_value (Root G P torsion f k) u.1 u.2 h) _

structure AddressProgramme (k : Key G P torsion f) (u : QueueTagged.Item (OI.K G)) where
  located : QueueTagged.lookupTree (Root G P torsion f k) u.1 = some u.2
  slot : FactorSaturation.Slots (Root G P torsion f k).2
  slotIdentity : slot = DeckAddressAccess.locatedSlot (Root G P torsion f k) u.1 u.2 located
  pathIdentity : FactorSaturation.path (Root G P torsion f k).2 slot = u.1
  occurrenceIdentity : FactorSaturation.slot (Root G P torsion f k).2 slot = u.2
  accessMacro : GeneralPowerExposure.PowerMacro P.table u.2.1.2
  macroIdentity : accessMacro = addressPower G P torsion f retained k u located
  toOriginal : RetainedBranch.ToOriginalProgramme G P u.2.1
  toOriginalIdentity : toOriginal = RetainedBranch.toOriginal G P u.2.1 accessMacro
  fromOriginal : RetainedBranch.FromOriginalProgramme G P u.2.1
  fromOriginalIdentity : fromOriginal = RetainedBranch.fromOriginal G P u.2.1
  savedRoot : RetainedCatalogue.occurrence G P torsion f
    (RetainedCatalogue.deckLabel G P torsion f k) = Root G P torsion f k
  retainedDescendants : ∀ q ∈ u.2.2.leaves, q ∈ RetainedCatalogue.family G P torsion f

def addressProgramme (k : Key G P torsion f) (u : QueueTagged.Item (OI.K G))
    (h : QueueTagged.lookupTree (Root G P torsion f k) u.1 = some u.2) :
    AddressProgramme G P torsion f retained k u := by
  let slot := DeckAddressAccess.locatedSlot (Root G P torsion f k) u.1 u.2 h
  let M := addressPower G P torsion f retained k u h
  refine ⟨h,slot,rfl,DeckAddressAccess.locatedSlot_path _ _ _ h,
    DeckAddressAccess.locatedSlot_value _ _ _ h,M,rfl,
    RetainedBranch.toOriginal G P u.2.1 M,rfl,RetainedBranch.fromOriginal G P u.2.1,rfl,
    RetainedCatalogue.deck_saved G P torsion f k,?_⟩
  intro q hq
  rw [RetainedCatalogue.family_exact]
  exact fullRetainedDeck_leaf P.family torsion f k q
    (FactorSaturation.stored_leaves_subset (QueueTagged.lookupTree_stored _ _ _ h) q hq)

/-- Full controlled equality includes the same actual machine, certified clock,
validity/length control and correctness at the exact frozen original-G endpoint. -/
theorem AddressProgramme.toOriginal_controlled (k : Key G P torsion f)
    (u : QueueTagged.Item (OI.K G)) (d : AddressProgramme G P torsion f retained k u) :
    d.toOriginal.controlled = (RetainedBranch.controlledToOriginal G P u.2.1 d.accessMacro) := by
  rw [d.toOriginalIdentity]
  rfl

theorem AddressProgramme.fromOriginal_controlled (k : Key G P torsion f)
    (u : QueueTagged.Item (OI.K G)) (d : AddressProgramme G P torsion f retained k u) :
    d.fromOriginal.controlled = (RetainedBranch.controlledFromOriginal G P u.2.1) := by
  rw [d.fromOriginalIdentity]
  rfl

structure TaggedProcessPhysical (S : TaggedState G P torsion f)
    (k : Key G P torsion f) (W : Multiset (QueueTagged.Item (OI.K G)))
    (e : QueueTagged.TreeTransition (S.work k) W) where
  projectedFocus : (S.inspection k W e).focus = e.focus.2
  focus : AddressProgramme G P torsion f retained k e.focus
  children : ∀ u ∈ e.children, AddressProgramme G P torsion f retained k u
  exposed : ∀ u ∈ e.exposed, AddressProgramme G P torsion f retained k u

def taggedProcessPhysical (S : TaggedState G P torsion f) (k : Key G P torsion f)
    (W : Multiset (QueueTagged.Item (OI.K G))) (e : QueueTagged.TreeTransition (S.work k) W) :
    TaggedProcessPhysical G P torsion f retained S k W e := by
  have hf := S.located k e.focus e.focus_mem
  exact ⟨S.inspection_focus k W e,addressProgramme G P torsion f retained k e.focus hf,
    (fun u hu => addressProgramme G P torsion f retained k u
      (e.children_located (Root G P torsion f k) hf u hu)),
    (fun u hu => addressProgramme G P torsion f retained k u
      (e.exposed_located (Root G P torsion f k) hf u hu))⟩

def TaggedEventPhysical {S T : TaggedState G P torsion f}
    (e : QueueTagged.Transition S T) : Type 1 := by
  cases e with
  | finish k hk hz => exact PUnit.{2}
  | process k hk W ht => exact TaggedProcessPhysical G P torsion f retained S k W ht

def taggedEventPhysical {S T : TaggedState G P torsion f} (e : QueueTagged.Transition S T) :
    TaggedEventPhysical G P torsion f retained e := by
  cases e with
  | finish k hk hz => exact PUnit.unit
  | process k hk W ht => exact taggedProcessPhysical G P torsion f retained S k W ht

variable (hm : 2 ≤ m)

def beforePalette (first : Bool) : Palette G :=
  if first then P else OccurrenceBatch.palette G P torsion f retained hm

/-- A joint receipt connects this exact stored-tree event to the internally
constructed occurrence palette, whole old-tree retention and both real machines. -/
structure TaggedJointEvent (first : Bool) {S T : TaggedState G P torsion f}
    (e : QueueTagged.Transition S T) where
  before : Palette G
  after : Palette G
  beforeIdentity : before = beforePalette G P torsion f retained hm first
  afterIdentity : after = OccurrenceBatch.palette G P torsion f retained hm
  retains : before.family ⊆ after.family
  oldSaved : ∀ i : Fin before.count, ∃ j : Fin after.count,
    (⟨⟨after.arity j.val,after.table j⟩,after.trees j⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨before.arity i.val,before.table i⟩,before.trees i⟩
  keyPending : e.projected.key ∈ S.queue.todo
  exactTransition : FrozenQueue.Step T.queue S.queue
  physical : TaggedEventPhysical G P torsion f retained e
  toOriginalControlled : HEq after.toOriginal.controlled
    (OccurrenceBatch.controlledToOriginal G P torsion f retained)
  fromOriginalControlled : HEq after.fromOriginal.controlled
    (ProgrammeRetained.controlledFromOriginal G P torsion f)
  toOriginalMachine : after.toOriginal.controlled.reduction.machine =
    (OccurrenceBatch.controlledToOriginal G P torsion f retained).reduction.machine
  fromOriginalMachine : after.fromOriginal.controlled.reduction.machine =
    (ProgrammeRetained.controlledFromOriginal G P torsion f).reduction.machine
  toOriginalClock : after.toOriginal.controlled.reduction.time =
    (OccurrenceBatch.controlledToOriginal G P torsion f retained).reduction.time
  fromOriginalClock : after.fromOriginal.controlled.reduction.time =
    (ProgrammeRetained.controlledFromOriginal G P torsion f).reduction.time

def taggedJointEvent (first : Bool) {S T : TaggedState G P torsion f}
    (e : QueueTagged.Transition S T) : TaggedJointEvent G P torsion f retained hm first e := by
  refine ⟨beforePalette G P torsion f retained hm first,
    OccurrenceBatch.palette G P torsion f retained hm,rfl,rfl,?_,?_,
    e.projected.key_pending,e.projected.step,taggedEventPhysical G P torsion f retained e,
    HEq.rfl,HEq.rfl,rfl,rfl,rfl,rfl⟩
  · cases first with
    | false => exact fun _ h => h
    | true =>
      rw [OccurrenceBatch.family_exact]
      exact fullRetainedDeck_retains P.family torsion f
  · cases first with
    | false => exact fun i => ⟨i,rfl⟩
    | true => exact fun i => ⟨RetainedCatalogue.oldLabel G P torsion f i,
        RetainedCatalogue.old_saved G P torsion f i⟩

def TaggedJointTrace (first : Bool) {S T : TaggedState G P torsion f}
    (h : QueueTagged.Trace S T) : Type 1 :=
  match h with
  | .nil _ => PUnit.{2}
  | .cons e rest => TaggedJointEvent G P torsion f retained hm first e × TaggedJointTrace false rest

def taggedJointTrace (first : Bool) {S T : TaggedState G P torsion f}
    (h : QueueTagged.Trace S T) : TaggedJointTrace G P torsion f retained hm first h :=
  match h with
  | .nil _ => PUnit.unit
  | .cons e rest => (taggedJointEvent G P torsion f retained hm first e,taggedJointTrace false rest)

/-- Every actually recorded event has its indexed charged physical receipt. -/
theorem recorded_physical {first : Bool} {S T A B : TaggedState G P torsion f}
    (h : QueueTagged.Trace S T) (J : TaggedJointTrace G P torsion f retained hm first h)
    (e : QueueTagged.Transition A B) (he : QueueTagged.EventIn h e) :
    Nonempty (TaggedEventPhysical G P torsion f retained e) := by
  induction he generalizing first with
  | head event rest => exact ⟨J.1.physical⟩
  | tail event rest actual recorded ih => exact ih J.2

/-- No joint trace, branch programme, minimum or future compiler is an input. -/
def savedTaggedJoint : TaggedJointTrace G P torsion f retained hm true
    (FullQueue.taggedExecution G P torsion f).trace :=
  taggedJointTrace G P torsion f retained hm true (FullQueue.taggedExecution G P torsion f).trace

@[simp] theorem exact_tagged_projection : (FullQueue.taggedExecution G P torsion f).trace.projected =
    (FullQueue.execution G P torsion f).trace := rfl

@[simp] theorem exact_result_queue : (OccurrenceBatch.result G P torsion f retained hm).finalQueue =
    (FullQueue.taggedExecution G P torsion f).finalState.queue := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceBatchJoint
