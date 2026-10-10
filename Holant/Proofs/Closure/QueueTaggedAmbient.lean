import Holant.Proofs.Closure.QueueAmbient
import Holant.Proofs.Closure.QueueTaggedJoint

/-! Address-exact original-G programme receipts for the SAME tagged ambient
trace used by all-arity history. Decoding preserves the full key and canonical
saved path; no native/ambient classical schedules are equated. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.AmbientQueue
open Holant Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature Holant.Tractable.AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)

abbrev TaggedState := QueueTagged.State (U:=Universe G P torsion f) (Root G P torsion f)

structure TaggedProcessPhysical (S : TaggedState G P torsion f) (j : Key G)
    (W : Multiset (QueueTagged.Item (OI.K G)))
    (e : QueueTagged.TreeTransition (S.work j) W) where
  nativeKey : FullDeckIndex P.family torsion f
  keyIdentity : HistoryCatalogue.embed P.family torsion f nativeKey = j
  rootIdentity : Root G P torsion f j = fullDeckRoot P.family torsion f nativeKey
  projectedFocus : (S.inspection j W e).focus = e.focus.2
  focus : FullQueue.AddressProgramme G P torsion f core hcore nativeKey e.focus
  children : ∀ u ∈ e.children, FullQueue.AddressProgramme G P torsion f core hcore nativeKey u
  exposed : ∀ u ∈ e.exposed, FullQueue.AddressProgramme G P torsion f core hcore nativeKey u

def taggedProcessPhysical (S : TaggedState G P torsion f) (j : Key G) (hj : j ∈ S.queue.todo)
    (W : Multiset (QueueTagged.Item (OI.K G)))
    (e : QueueTagged.TreeTransition (S.work j) W) :
    TaggedProcessPhysical G P torsion f core hcore S j W e := by
  let k := decode G P torsion f j (S.queue.within hj)
  have hr := root_binding G P torsion f j (S.queue.within hj)
  have hf : QueueTagged.lookupTree (fullDeckRoot P.family torsion f k) e.focus.1 = some e.focus.2 := by
    rw [←hr]
    exact S.located j e.focus e.focus_mem
  exact ⟨k,decode_binding G P torsion f j (S.queue.within hj),hr,S.inspection_focus j W e,
    FullQueue.addressProgramme G P torsion f core hcore k e.focus hf,
    (fun u hu => FullQueue.addressProgramme G P torsion f core hcore k u
      (e.children_located (fullDeckRoot P.family torsion f k) hf u hu)),
    (fun u hu => FullQueue.addressProgramme G P torsion f core hcore k u
      (e.exposed_located (fullDeckRoot P.family torsion f k) hf u hu))⟩

def TaggedEventPhysical {S T : TaggedState G P torsion f} (e : QueueTagged.Transition S T) : Type 1 :=
by
  cases e with
  | finish j hj hz => exact PUnit.{2}
  | process j hj W ht => exact TaggedProcessPhysical G P torsion f core hcore S j W ht

def taggedEventPhysical {S T : TaggedState G P torsion f} (e : QueueTagged.Transition S T) :
    TaggedEventPhysical G P torsion f core hcore e := by
  cases e with
  | finish j hj hz => exact PUnit.unit
  | process j hj W ht => exact taggedProcessPhysical G P torsion f core hcore S j hj W ht

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

/-- Exact addressed receipt factory for the history's actual stored trace. -/
def savedTaggedJoint : TaggedJointTrace G P torsion f core hcore hm true
    (HistoryCatalogue.exhaust P.family torsion f).tagged.trace :=
  taggedJointTrace G P torsion f core hcore hm true
    (HistoryCatalogue.exhaust P.family torsion f).tagged.trace

@[simp] theorem exact_tagged_projection :
    (HistoryCatalogue.exhaust P.family torsion f).tagged.trace.projected =
      (HistoryCatalogue.exhaust P.family torsion f).trace := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.AmbientQueue
end
