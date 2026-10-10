import Holant.Proofs.Closure.QueueJoint
import Holant.Proofs.Closure.DeckAddressAccess

/-! Canonical-address joint receipts for the actual tagged producer. These
retain path identities even when different saved addresses have equal leaves.
Every actual focus and child uses its computed saved slot's exact split graph. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.FullQueue
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature Holant.Tractable.AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)

/-- A physically charged source boundary at one EXACT saved address. -/
structure AddressProgramme (k : Key G P torsion f) (u : QueueTagged.Item (OI.K G)) where
  located : QueueTagged.lookupTree (Root G P torsion f k) u.1 = some u.2
  slot : FactorSaturation.Slots (Root G P torsion f k).2
  slotIdentity : slot = DeckAddressAccess.locatedSlot (Root G P torsion f k) u.1 u.2 located
  pathIdentity : FactorSaturation.path (Root G P torsion f k).2 slot = u.1
  occurrenceIdentity : FactorSaturation.slot (Root G P torsion f k).2 slot = u.2
  accessMacro : GeneralPowerExposure.PowerMacro P.table u.2.1.2
  macroIdentity : accessMacro = DeckAddressAccess.deckAddressPower G P torsion f core hcore k u.1 u.2 located
  toOriginal : RetainedBranch.ToOriginalProgramme G P u.2.1
  toOriginalIdentity : toOriginal = RetainedBranch.toOriginal G P u.2.1 accessMacro
  fromOriginal : RetainedBranch.FromOriginalProgramme G P u.2.1
  fromOriginalIdentity : fromOriginal = RetainedBranch.fromOriginal G P u.2.1
  savedRoot : RetainedCatalogue.occurrence G P torsion f
    (RetainedCatalogue.deckLabel G P torsion f k) = Root G P torsion f k
  retainedDescendants : ∀ g ∈ u.2.2.leaves, g ∈ RetainedCatalogue.family G P torsion f

def addressProgramme (k : Key G P torsion f) (u : QueueTagged.Item (OI.K G))
    (h : QueueTagged.lookupTree (Root G P torsion f k) u.1 = some u.2) :
    AddressProgramme G P torsion f core hcore k u := by
  let slot := DeckAddressAccess.locatedSlot (Root G P torsion f k) u.1 u.2 h
  let M := DeckAddressAccess.deckAddressPower G P torsion f core hcore k u.1 u.2 h
  refine ⟨h,slot,rfl,DeckAddressAccess.locatedSlot_path _ _ _ h,
    DeckAddressAccess.locatedSlot_value _ _ _ h,M,rfl,
    RetainedBranch.toOriginal G P u.2.1 M,rfl,RetainedBranch.fromOriginal G P u.2.1,rfl,
    RetainedCatalogue.deck_saved G P torsion f k,?_⟩
  intro g hg
  rw [RetainedCatalogue.family_exact]
  exact fullRetainedDeck_leaf P.family torsion f k g
    (FactorSaturation.stored_leaves_subset (QueueTagged.lookupTree_stored _ _ _ h) g hg)

abbrev TaggedState := QueueTagged.State (U:=Universe G P torsion f) (Root G P torsion f)

/-- The exact projected queue inspection and its canonical focus/child paths
share one receipt. All child boundaries are charged, including open composites. -/
structure TaggedProcessPhysical (S : TaggedState G P torsion f)
    (k : Key G P torsion f) (W : Multiset (QueueTagged.Item (OI.K G)))
    (e : QueueTagged.TreeTransition (S.work k) W) where
  projectedFocus : (S.inspection k W e).focus = e.focus.2
  focus : AddressProgramme G P torsion f core hcore k e.focus
  children : ∀ u ∈ e.children, AddressProgramme G P torsion f core hcore k u
  exposed : ∀ u ∈ e.exposed, AddressProgramme G P torsion f core hcore k u

def taggedProcessPhysical (S : TaggedState G P torsion f) (k : Key G P torsion f)
    (W : Multiset (QueueTagged.Item (OI.K G)))
    (e : QueueTagged.TreeTransition (S.work k) W) :
    TaggedProcessPhysical G P torsion f core hcore S k W e := by
  have hf := S.located k e.focus e.focus_mem
  exact ⟨S.inspection_focus k W e,addressProgramme G P torsion f core hcore k e.focus hf,
    (fun u hu => addressProgramme G P torsion f core hcore k u
      (e.children_located (Root G P torsion f k) hf u hu)),
    (fun u hu => addressProgramme G P torsion f core hcore k u
      (e.exposed_located (Root G P torsion f k) hf u hu))⟩

def TaggedEventPhysical {S T : TaggedState G P torsion f}
    (e : QueueTagged.Transition S T) : Type 1 :=
by
  cases e with
  | finish k hk hz => exact PUnit.{2}
  | process k hk W ht => exact TaggedProcessPhysical G P torsion f core hcore S k W ht

def taggedEventPhysical {S T : TaggedState G P torsion f} (e : QueueTagged.Transition S T) :
    TaggedEventPhysical G P torsion f core hcore e := by
  cases e with
  | finish k hk hz => exact PUnit.unit
  | process k hk W ht => exact taggedProcessPhysical G P torsion f core hcore S k W ht

variable (hm : 2 ≤ m)

structure TaggedJointEvent (first : Bool) {S T : TaggedState G P torsion f}
    (e : QueueTagged.Transition S T) where
  palettes : JointEvent G P torsion f core hcore hm first e.projected
  physical : TaggedEventPhysical G P torsion f core hcore e

def taggedJointEvent (first : Bool) {S T : TaggedState G P torsion f}
    (e : QueueTagged.Transition S T) : TaggedJointEvent G P torsion f core hcore hm first e :=
  ⟨jointEvent G P torsion f core hcore hm first e.projected S.storedFrontier,
    taggedEventPhysical G P torsion f core hcore e⟩

def TaggedJointTrace (first : Bool) {S T : TaggedState G P torsion f}
    (h : QueueTagged.Trace S T) : Type 1 :=
  match h with
  | .nil _ => PUnit.{2}
  | .cons e rest => TaggedJointEvent G P torsion f core hcore hm first e ×
      TaggedJointTrace false rest

def taggedJointTrace (first : Bool) {S T : TaggedState G P torsion f}
    (h : QueueTagged.Trace S T) : TaggedJointTrace G P torsion f core hcore hm first h :=
  match h with
  | .nil _ => PUnit.unit
  | .cons e rest => (taggedJointEvent G P torsion f core hcore hm first e,
      taggedJointTrace false rest)

/-- Every event actually recorded in this trace carries its corresponding
canonical-address physical receipt in the constructed joint trace. -/
theorem recorded_physical {first : Bool} {S T A B : TaggedState G P torsion f}
    (h : QueueTagged.Trace S T) (J : TaggedJointTrace G P torsion f core hcore hm first h)
    (e : QueueTagged.Transition A B) (he : QueueTagged.EventIn h e) :
    Nonempty (TaggedEventPhysical G P torsion f core hcore e) := by
  induction he generalizing first with
  | head event rest => exact ⟨J.1.physical⟩
  | tail event rest actual recorded ih => exact ih J.2

/-- Internally constructed addressed/programme/palette trace, whose exact
projection is the trace returned by the closed batch producer. -/
def savedTaggedJoint : TaggedJointTrace G P torsion f core hcore hm true
    (taggedExecution G P torsion f).trace :=
  taggedJointTrace G P torsion f core hcore hm true (taggedExecution G P torsion f).trace

@[simp] theorem exact_tagged_projection : (taggedExecution G P torsion f).trace.projected =
    (execution G P torsion f).trace := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.FullQueue
end
