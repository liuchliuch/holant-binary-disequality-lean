import Holant.Proofs.Closure.OccurrenceBatchJoint

/-! Reconstructed exact leaf bindings for the SAME nonminimum tagged execution.
The canonical path first determines its stored slot; the unique leaf index then
binds the actual installed label, whole saved occurrence, macro and both physical
programmes. Equal table values at different paths remain different resources. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceBatchJointLeaves
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction
open OccurrenceBatchJoint

variable {L : Type} [Field L]

def leafConstructor (u : TreeOccurrence L) : Bool :=
  match u.2 with
  | .leaf _ _ => true
  | .split _ _ _ => false

/-- A leaf-shaped saved slot is one genuine indexed leaf of THAT exact tree. -/
theorem slot_leaf_index {f : AnySignature L} (t : FactorTree f)
    (i : FactorSaturation.Slots t) (hl : leafConstructor (FactorSaturation.slot t i) = true) :
    ∃ j : FactorSaturation.Leaves t, FactorSaturation.leafSlot t j = i := by
  induction t with
  | leaf f prime =>
    change Unit at i
    cases i
    exact ⟨(),rfl⟩
  | split sp left right il ir =>
    rcases i with root | (i | i)
    · simp [leafConstructor,FactorSaturation.slot] at hl
    · obtain ⟨j,hj⟩ := il i hl
      exact ⟨Sum.inl j,congrArg (fun i => Sum.inr (Sum.inl i)) hj⟩
    · obtain ⟨j,hj⟩ := ir i hl
      exact ⟨Sum.inr j,congrArg (fun i => Sum.inr (Sum.inr i)) hj⟩

theorem leafSlot_injective {f : AnySignature L} (t : FactorTree f) :
    Function.Injective (FactorSaturation.leafSlot t) := by
  induction t with
  | leaf =>
    intro a b h
    change Unit at a b
    cases a
    cases b
    rfl
  | split sp left right il ir =>
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (il (Sum.inl.inj (Sum.inr.inj h)))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (ir (Sum.inr.inj (Sum.inr.inj h)))

theorem leafSlot_constructor {f : AnySignature L} (t : FactorTree f)
    (j : FactorSaturation.Leaves t) :
    leafConstructor (FactorSaturation.slot t (FactorSaturation.leafSlot t j)) = true := by
  induction t with
  | leaf => rfl
  | split sp left right il ir =>
    cases j with
    | inl j => exact il j
    | inr j => exact ir j

universe u v
private theorem sigma_transport {A : Type u} {C : A → Type v} {a b : A}
    (h : a=b) (x : C a) : (⟨b,h ▸ x⟩ : Sigma C) = ⟨a,x⟩ := by
  cases h
  rfl

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (retained : (⟨m+2,f⟩ : AnySignature (OI.K G)) ∈ P.family)

structure LeafBinding (k : Key G P torsion f) (u : QueueTagged.Item (OI.K G))
    (d : AddressProgramme G P torsion f retained k u) : Type 1 where
  leafIndex : FactorSaturation.Leaves (Root G P torsion f k).2
  leafSlot : FactorSaturation.leafSlot (Root G P torsion f k).2 leafIndex = d.slot
  path : FactorSaturation.path (Root G P torsion f k).2
    (FactorSaturation.leafSlot (Root G P torsion f k).2 leafIndex) = u.1
  wholeOccurrence : FactorSaturation.slot (Root G P torsion f k).2
    (FactorSaturation.leafSlot (Root G P torsion f k).2 leafIndex) = u.2
  label : Fin (RetainedCatalogue.count G P torsion f)
  labelIdentity : label = RetainedCatalogue.leafLabel G P torsion f k leafIndex
  saved : RetainedCatalogue.occurrence G P torsion f label = u.2
  installedPower : (⟨u.2,d.accessMacro⟩ :
    Σ v : TreeOccurrence (OI.K G), GeneralPowerExposure.PowerMacro P.table v.1.2) =
    ⟨FactorSaturation.slot (Root G P torsion f k).2
      (FactorSaturation.leafSlot (Root G P torsion f k).2 leafIndex),
      OccurrenceBatch.indexPower G P torsion f retained (.inr ⟨k,leafIndex⟩)⟩
  installedForward : (⟨u.2,d.toOriginal⟩ :
    Σ v : TreeOccurrence (OI.K G), RetainedBranch.ToOriginalProgramme G P v.1) =
    ⟨FactorSaturation.slot (Root G P torsion f k).2
      (FactorSaturation.leafSlot (Root G P torsion f k).2 leafIndex),
      RetainedBranch.toOriginal G P
        (FactorSaturation.slot (Root G P torsion f k).2
          (FactorSaturation.leafSlot (Root G P torsion f k).2 leafIndex)).1
        (OccurrenceBatch.indexPower G P torsion f retained (.inr ⟨k,leafIndex⟩))⟩
  installedReverse : (⟨u.2,d.fromOriginal⟩ :
    Σ v : TreeOccurrence (OI.K G), RetainedBranch.FromOriginalProgramme G P v.1) =
    ⟨FactorSaturation.slot (Root G P torsion f k).2
      (FactorSaturation.leafSlot (Root G P torsion f k).2 leafIndex),
      RetainedBranch.fromOriginal G P
        (FactorSaturation.slot (Root G P torsion f k).2
          (FactorSaturation.leafSlot (Root G P torsion f k).2 leafIndex)).1⟩

/-- Classical extraction happens only AFTER computing the unique stored slot. -/
def leafBinding (k : Key G P torsion f) (u : QueueTagged.Item (OI.K G))
    (d : AddressProgramme G P torsion f retained k u) (hl : leafConstructor u.2 = true) :
    LeafBinding G P torsion f retained k u d := by
  have hs : leafConstructor (FactorSaturation.slot (Root G P torsion f k).2 d.slot) = true := by
    rw [d.occurrenceIdentity]
    exact hl
  let j := Classical.choose (slot_leaf_index (Root G P torsion f k).2 d.slot hs)
  have hj : FactorSaturation.leafSlot (Root G P torsion f k).2 j = d.slot :=
    Classical.choose_spec (slot_leaf_index (Root G P torsion f k).2 d.slot hs)
  have hp : FactorSaturation.path (Root G P torsion f k).2
      (FactorSaturation.leafSlot (Root G P torsion f k).2 j) = u.1 := by
    rw [hj]
    exact d.pathIdentity
  have hv : FactorSaturation.slot (Root G P torsion f k).2
      (FactorSaturation.leafSlot (Root G P torsion f k).2 j) = u.2 := by
    rw [hj]
    exact d.occurrenceIdentity
  have power : (⟨u.2,d.accessMacro⟩ :
      Σ v : TreeOccurrence (OI.K G), GeneralPowerExposure.PowerMacro P.table v.1.2) =
      ⟨FactorSaturation.slot (Root G P torsion f k).2
        (FactorSaturation.leafSlot (Root G P torsion f k).2 j),
        OccurrenceBatch.indexPower G P torsion f retained (.inr ⟨k,j⟩)⟩ := by
    rw [d.macroIdentity]
    have h := addressPower_pair G P torsion f retained k u d.located
    rw [←d.slotIdentity,←hj] at h
    exact h
  refine ⟨j,hj,hp,hv,RetainedCatalogue.leafLabel G P torsion f k j,rfl,
    (RetainedCatalogue.leaf_saved G P torsion f k j).trans hv,power,?_,?_⟩
  · rw [d.toOriginalIdentity]
    exact congrArg (fun x : Σ v : TreeOccurrence (OI.K G),
        GeneralPowerExposure.PowerMacro P.table v.1.2 =>
      (⟨x.1,RetainedBranch.toOriginal G P x.1.1 x.2⟩ :
        Σ v : TreeOccurrence (OI.K G), RetainedBranch.ToOriginalProgramme G P v.1)) power
  · rw [d.fromOriginalIdentity]
    exact congrArg (fun v : TreeOccurrence (OI.K G) =>
      (⟨v,RetainedBranch.fromOriginal G P v.1⟩ :
        Σ v : TreeOccurrence (OI.K G), RetainedBranch.FromOriginalProgramme G P v.1)) hv.symm

theorem LeafBinding.unique_index (k : Key G P torsion f) (u : QueueTagged.Item (OI.K G))
    (d : AddressProgramme G P torsion f retained k u)
    (x y : LeafBinding G P torsion f retained k u d) : x.leafIndex = y.leafIndex :=
  leafSlot_injective _ (x.leafSlot.trans y.leafSlot.symm)

theorem distinct_paths_distinct_labels (k : Key G P torsion f)
    (u v : QueueTagged.Item (OI.K G))
    (du : AddressProgramme G P torsion f retained k u) (dv : AddressProgramme G P torsion f retained k v)
    (x : LeafBinding G P torsion f retained k u du) (y : LeafBinding G P torsion f retained k v dv)
    (paths : u.1 ≠ v.1) : x.label ≠ y.label := by
  intro labels
  rw [x.labelIdentity,y.labelIdentity] at labels
  have hj := RetainedCatalogue.leafLabel_injective G P torsion f k labels
  apply paths
  exact x.path.symm.trans ((congrArg (fun j => FactorSaturation.path (Root G P torsion f k).2
    (FactorSaturation.leafSlot (Root G P torsion f k).2 j)) hj).trans y.path)

/-- Every emitted tree leaf preserves the actual stored leaf constructor. -/
theorem treeLeaves_leaf_constructor {g : AnySignature (OI.K G)} (t : FactorTree g)
    (p : List Bool) (u : QueueTagged.Item (OI.K G))
    (hu : u ∈ QueueTagged.treeLeaves t p) : leafConstructor u.2 = true := by
  induction t generalizing p with
  | leaf g prime =>
    have he : u = (p,⟨g,FactorTree.leaf g prime⟩) := by
      simpa only [QueueTagged.treeLeaves,Multiset.mem_singleton] using hu
    subst u
    rfl
  | split sp left right il ir =>
    simp only [QueueTagged.treeLeaves,Multiset.mem_add] at hu
    rcases hu with hu | hu
    · exact il _ hu
    · exact ir _ hu

theorem closedLeaves_leaf_constructor (t u : QueueTagged.Item (OI.K G))
    (hu : u ∈ QueueTagged.closedLeaves t) : leafConstructor u.2 = true := by
  unfold QueueTagged.closedLeaves at hu
  split_ifs at hu with hOpen
  · simp at hu
  · exact treeLeaves_leaf_constructor G t.2.2 t.1 u hu

/-- Split events also emit actual closed unary children immediately. This
covers those SAME emitted addresses rather than assuming all split exposure empty. -/
theorem exposed_leaf_constructor {W V : Multiset (QueueTagged.Item (OI.K G))}
    (e : QueueTagged.TreeTransition W V) (u : QueueTagged.Item (OI.K G))
    (hu : u ∈ e.exposed) : leafConstructor u.2 = true := by
  cases e with
  | leaf p g prime positive rest =>
    have he : u = (p,⟨g,FactorTree.leaf g prime⟩) := by
      simpa only [QueueTagged.TreeTransition.exposed,Multiset.mem_singleton] using hu
    subst u
    rfl
  | split p sp left right rest =>
    simp only [QueueTagged.TreeTransition.exposed,Multiset.mem_add] at hu
    rcases hu with hu | hu
    · exact closedLeaves_leaf_constructor G _ u hu
    · exact closedLeaves_leaf_constructor G _ u hu

structure ProcessLeafBindings (S : TaggedState G P torsion f)
    (k : Key G P torsion f) (W : Multiset (QueueTagged.Item (OI.K G)))
    (e : QueueTagged.TreeTransition (S.work k) W)
    (physical : TaggedProcessPhysical G P torsion f retained S k W e) : Type 1 where
  exposed : ∀ u (hu : u ∈ e.exposed),
    LeafBinding G P torsion f retained k u (physical.exposed u hu)

def processLeafBindings (S : TaggedState G P torsion f)
    (k : Key G P torsion f) (W : Multiset (QueueTagged.Item (OI.K G)))
    (e : QueueTagged.TreeTransition (S.work k) W)
    (physical : TaggedProcessPhysical G P torsion f retained S k W e) :
    ProcessLeafBindings G P torsion f retained S k W e physical :=
  ⟨fun u hu => leafBinding G P torsion f retained k u (physical.exposed u hu)
    (exposed_leaf_constructor G e u hu)⟩

def EventLeafBindings {S T : TaggedState G P torsion f}
    (e : QueueTagged.Transition S T) (physical : TaggedEventPhysical G P torsion f retained e) : Type 1 := by
  cases e with
  | finish k hk hz => exact PUnit.{2}
  | process k hk W ht => exact ProcessLeafBindings G P torsion f retained S k W ht physical

def eventLeafBindings {S T : TaggedState G P torsion f}
    (e : QueueTagged.Transition S T) (physical : TaggedEventPhysical G P torsion f retained e) :
    EventLeafBindings G P torsion f retained e physical := by
  cases e with
  | finish k hk hz => exact PUnit.unit
  | process k hk W ht => exact processLeafBindings G P torsion f retained S k W ht physical

variable (hm : 2 ≤ m)

structure JointEventWithLeaves (first : Bool) {S T : TaggedState G P torsion f}
    (e : QueueTagged.Transition S T) where
  joint : TaggedJointEvent G P torsion f retained hm first e
  leaves : EventLeafBindings G P torsion f retained e joint.physical

def jointEventWithLeaves (first : Bool) {S T : TaggedState G P torsion f}
    (e : QueueTagged.Transition S T) : JointEventWithLeaves G P torsion f retained hm first e :=
  let joint := taggedJointEvent G P torsion f retained hm first e
  ⟨joint,eventLeafBindings G P torsion f retained e joint.physical⟩

def JointTraceWithLeaves (first : Bool) {S T : TaggedState G P torsion f}
    (h : QueueTagged.Trace S T) : Type 1 :=
  match h with
  | .nil _ => PUnit.{2}
  | .cons e rest => JointEventWithLeaves G P torsion f retained hm first e × JointTraceWithLeaves false rest

def jointTraceWithLeaves (first : Bool) {S T : TaggedState G P torsion f}
    (h : QueueTagged.Trace S T) : JointTraceWithLeaves G P torsion f retained hm first h :=
  match h with
  | .nil _ => PUnit.unit
  | .cons e rest => (jointEventWithLeaves G P torsion f retained hm first e,jointTraceWithLeaves false rest)

/-- SAME projected saved exhaustion, with every concrete exposed leaf bound
to its installed label, full macro and both actual original-G programmes. -/
def savedJointWithLeaves : JointTraceWithLeaves G P torsion f retained hm true
    (FullQueue.taggedExecution G P torsion f).trace :=
  jointTraceWithLeaves G P torsion f retained hm true (FullQueue.taggedExecution G P torsion f).trace

end Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceBatchJointLeaves
