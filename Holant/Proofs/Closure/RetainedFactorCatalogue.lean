import Holant.Proofs.Closure.RetainedCatalogue
import Holant.Proofs.Reductions.FactorSaturation.Catalogue

/-! NEW UNVERIFIED old-tree-preserving saturation for one ACTUAL source output.
Only q's exact FactorTree is chosen; every old whole tree is copied literally.
All root/proper occurrences are appended, so every stored factor is a real
retained label, with its power macro derived from that same source tree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedFactorCatalogue
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (q : AnySignature (OI.K G)) (nonzero : q.2 ≠ 0)

def tree : FactorTree q := Classical.choice (exists_factorTree q nonzero)
abbrev NewIndex := FactorSaturation.Slots (tree G q nonzero)
def newOccurrence (j : NewIndex G q nonzero) : TreeOccurrence (OI.K G) :=
  FactorSaturation.slot (tree G q nonzero) j
def addedCount := Fintype.card (NewIndex G q nonzero)
def enumerate : Fin (addedCount G q nonzero) ≃ NewIndex G q nonzero := (Fintype.equivFin _).symm
def entry (j : Fin (addedCount G q nonzero)) := newOccurrence G q nonzero (enumerate G q nonzero j)
def count := P.count + addedCount G q nonzero

def lookup (n : ℕ) : AnySignature (OI.K G) :=
  if h : n < P.count then ⟨P.arity n,P.table ⟨n,h⟩⟩
  else if h : n < count G P q nonzero then
    (entry G q nonzero ⟨n-P.count,by unfold count at h; omega⟩).1 else ⟨0,0⟩
def arity (n : ℕ) := (lookup G P q nonzero n).1
def table (i : Fin (count G P q nonzero)) : Signature (OI.K G) (arity G P q nonzero i.val) :=
  (lookup G P q nonzero i.val).2

@[simp] theorem lookup_old (i : Fin P.count) : lookup G P q nonzero i.val =
    (⟨P.arity i.val,P.table i⟩ : AnySignature (OI.K G)) := by simp only [lookup,dif_pos i.isLt]
@[simp] theorem lookup_new (j : Fin (addedCount G q nonzero)) : lookup G P q nonzero (P.count+j.val) =
    (entry G q nonzero j).1 := by
  have hn : ¬ P.count+j.val < P.count := by omega
  have hl : P.count+j.val < count G P q nonzero := by unfold count; omega
  simp only [lookup,dif_neg hn,dif_pos hl,Nat.add_sub_cancel_left]

def trees (i : Fin (count G P q nonzero)) :
    FactorTree (⟨arity G P q nonzero i.val,table G P q nonzero i⟩ : AnySignature (OI.K G)) :=
  if h : i.val < P.count then
    RetainedCatalogue.transportTree (lookup_old G P q nonzero ⟨i.val,h⟩).symm (P.trees ⟨i.val,h⟩)
  else
    let j : Fin (addedCount G q nonzero) := ⟨i.val-P.count,by have := i.isLt; unfold count at this; omega⟩
    RetainedCatalogue.transportTree (by
      change (entry G q nonzero j).1 = lookup G P q nonzero i.val
      have hn : i.val = P.count+j.val := by dsimp [j]; omega
      rw [hn]
      exact (lookup_new G P q nonzero j).symm) (entry G q nonzero j).2

def occurrence (i : Fin (count G P q nonzero)) : TreeOccurrence (OI.K G) :=
  ⟨⟨arity G P q nonzero i.val,table G P q nonzero i⟩,trees G P q nonzero i⟩
def oldLabel (i : Fin P.count) : Fin (count G P q nonzero) := ⟨i.val,by unfold count; omega⟩
def newLabel (j : Fin (addedCount G q nonzero)) : Fin (count G P q nonzero) :=
  ⟨P.count+j.val,by unfold count; omega⟩
def slotLabel (j : NewIndex G q nonzero) := newLabel G P q nonzero ((enumerate G q nonzero).symm j)
def rootLabel := slotLabel G P q nonzero (savedRootSlot (tree G q nonzero))

@[simp] theorem old_saved (i : Fin P.count) : occurrence G P q nonzero (oldLabel G P q nonzero i) =
    (⟨⟨P.arity i.val,P.table i⟩,P.trees i⟩ : TreeOccurrence (OI.K G)) := by
  change (⟨lookup G P q nonzero i.val,trees G P q nonzero (oldLabel G P q nonzero i)⟩ : TreeOccurrence _) = _
  simp only [trees,oldLabel,dif_pos i.isLt]
  exact RetainedCatalogue.transportTree_saved (L:=OI.K G) _ _
@[simp] theorem new_saved (j : Fin (addedCount G q nonzero)) :
    occurrence G P q nonzero (newLabel G P q nonzero j) = entry G q nonzero j := by
  have hn : ¬ P.count+j.val < P.count := by omega
  change (⟨lookup G P q nonzero (P.count+j.val),trees G P q nonzero (newLabel G P q nonzero j)⟩ : TreeOccurrence _) = _
  simp only [trees,newLabel,dif_neg hn]
  let jj : Fin (addedCount G q nonzero) := ⟨P.count+j.val-P.count,by omega⟩
  have hj : jj = j := by apply Fin.ext; dsimp [jj]; omega
  trans entry G q nonzero jj
  · exact RetainedCatalogue.transportTree_saved (L:=OI.K G) _ _
  · exact congrArg (entry G q nonzero) hj
@[simp] theorem slot_saved (j : NewIndex G q nonzero) :
    occurrence G P q nonzero (slotLabel G P q nonzero j) = newOccurrence G q nonzero j := by
  unfold slotLabel
  rw [new_saved]
  simp only [entry,Equiv.apply_symm_apply]
@[simp] theorem root_saved : occurrence G P q nonzero (rootLabel G P q nonzero) =
    (⟨q,tree G q nonzero⟩ : TreeOccurrence (OI.K G)) :=
  (slot_saved G P q nonzero _).trans (savedRootSlot_value _)

theorem oldLabel_injective : Function.Injective (oldLabel G P q nonzero) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin (count G P q nonzero) => z.val) h
theorem newLabel_injective : Function.Injective (newLabel G P q nonzero) := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  change P.count+i.val = P.count+j.val at he
  omega

theorem slotLabel_injective : Function.Injective (slotLabel G P q nonzero) := by
  intro i j h
  exact (enumerate G q nonzero).symm.injective (newLabel_injective G P q nonzero h)

theorem old_new_disjoint (i : Fin P.count) (j : Fin (addedCount G q nonzero)) :
    oldLabel G P q nonzero i ≠ newLabel G P q nonzero j := by
  intro h
  have hv := congrArg (fun z : Fin (count G P q nonzero) => z.val) h
  change i.val = P.count+j.val at hv
  have := i.isLt
  omega

/-- Dense labels partition into the exact copied old labels and the exact
addressed slots, without identifying duplicate table values. -/
theorem label_partition (i : Fin (count G P q nonzero)) :
    (∃ j : Fin P.count, oldLabel G P q nonzero j = i) ∨
      ∃ j : NewIndex G q nonzero, slotLabel G P q nonzero j = i := by
  by_cases hi : i.val < P.count
  · exact Or.inl ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
  · let j : Fin (addedCount G q nonzero) := ⟨i.val-P.count,by
      have := i.isLt
      unfold count at this
      omega⟩
    refine Or.inr ⟨enumerate G q nonzero j,?_⟩
    simp only [slotLabel,Equiv.symm_apply_apply]
    apply Fin.ext
    dsimp [newLabel,j]
    omega

def family : SignatureFamily (OI.K G) := Set.range
  (fun i : Fin (count G P q nonzero) => (⟨arity G P q nonzero i.val,table G P q nonzero i⟩ : AnySignature (OI.K G)))

theorem old_retained (i : Fin P.count) : (⟨P.arity i.val,P.table i⟩ : AnySignature (OI.K G)) ∈ family G P q nonzero :=
  ⟨oldLabel G P q nonzero i,congrArg Sigma.fst (old_saved G P q nonzero i)⟩
theorem slot_retained (j : NewIndex G q nonzero) : (newOccurrence G q nonzero j).1 ∈ family G P q nonzero :=
  ⟨slotLabel G P q nonzero j,congrArg Sigma.fst (slot_saved G P q nonzero j)⟩
theorem root_retained : q ∈ family G P q nonzero :=
  ⟨rootLabel G P q nonzero,congrArg Sigma.fst (root_saved G P q nonzero)⟩

/-- Exact mathematical carrier: old literal tables plus EVERY stored slot of
only q's chosen tree. Composite slots are retained intentionally here. -/
theorem family_exact : family G P q nonzero = P.family ∪
    Set.range (fun j : NewIndex G q nonzero => (newOccurrence G q nonzero j).1) := by
  ext u
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val < P.count
    · left
      change lookup G P q nonzero i.val ∈ P.family
      rw [lookup_old G P q nonzero ⟨i.val,hi⟩]
      exact ⟨⟨i.val,hi⟩,rfl⟩
    · right
      let j : Fin (addedCount G q nonzero) := ⟨i.val-P.count,by have := i.isLt; unfold count at this; omega⟩
      have hn : newLabel G P q nonzero j = i := Fin.ext (by dsimp [newLabel,j]; omega)
      exact ⟨enumerate G q nonzero j,(congrArg Sigma.fst (new_saved G P q nonzero j)).symm.trans
        (congrArg (fun z => (occurrence G P q nonzero z).1) hn)⟩
  · rintro (hu | ⟨j,rfl⟩)
    · obtain ⟨i,rfl⟩ := hu
      exact old_retained G P q nonzero i
    · exact slot_retained G P q nonzero j

theorem source_retained : P.family ⊆ family G P q nonzero := by
  intro u hu
  rw [family_exact]
  exact Or.inl hu

theorem new_positive (positive : 0 < q.1) (j : NewIndex G q nonzero) :
    0 < (newOccurrence G q nonzero j).1.1 :=
  FactorSaturation.stored_positive (FactorSaturation.slot_stored _ _) positive

theorem new_nonzero (j : NewIndex G q nonzero) : (newOccurrence G q nonzero j).1.2 ≠ 0 :=
  FactorSaturation.stored_nonzero (FactorSaturation.slot_stored _ _) nonzero

theorem positive (positive : 0 < q.1) (i : Fin (count G P q nonzero)) : 0 < arity G P q nonzero i.val := by
  by_cases hi : i.val < P.count
  · change 0 < (lookup G P q nonzero i.val).1
    rw [lookup_old G P q nonzero ⟨i.val,hi⟩]
    exact P.positive ⟨i.val,hi⟩
  · let j : Fin (addedCount G q nonzero) := ⟨i.val-P.count,by have := i.isLt; unfold count at this; omega⟩
    have hn : i.val = P.count+j.val := by dsimp [j]; omega
    change 0 < (lookup G P q nonzero i.val).1
    rw [hn,lookup_new]
    exact new_positive G q nonzero positive _

theorem table_nonzero (i : Fin (count G P q nonzero)) : table G P q nonzero i ≠ 0 := by
  by_cases hi : i.val < P.count
  · have he := lookup_old G P q nonzero ⟨i.val,hi⟩
    change (lookup G P q nonzero i.val).2 ≠ 0
    exact Eq.mpr (congrArg (fun u : AnySignature (OI.K G) => u.2 ≠ 0) he) (P.nonzero ⟨i.val,hi⟩)
  · let j : Fin (addedCount G q nonzero) := ⟨i.val-P.count,by have := i.isLt; unfold count at this; omega⟩
    have hn : i.val = P.count+j.val := by dsimp [j]; omega
    have he : lookup G P q nonzero i.val = (entry G q nonzero j).1 := by
      rw [hn]
      exact lookup_new G P q nonzero j
    change (lookup G P q nonzero i.val).2 ≠ 0
    exact Eq.mpr (congrArg (fun u : AnySignature (OI.K G) => u.2 ≠ 0) he) (new_nonzero G q nonzero _)

theorem leaves_retained (i : Fin (count G P q nonzero)) (u : AnySignature (OI.K G))
    (hu : u ∈ (trees G P q nonzero i).leaves) : u ∈ family G P q nonzero := by
  by_cases hi : i.val < P.count
  · have hn : oldLabel G P q nonzero ⟨i.val,hi⟩ = i := Fin.ext rfl
    rw [←hn] at hu
    have he := congrArg (fun z : TreeOccurrence (OI.K G) => z.2.leaves) (old_saved G P q nonzero ⟨i.val,hi⟩)
    change (trees G P q nonzero (oldLabel G P q nonzero ⟨i.val,hi⟩)).leaves =
      (P.trees ⟨i.val,hi⟩).leaves at he
    rw [he] at hu
    obtain ⟨j,hj⟩ := P.leavesRetained _ _ hu
    exact hj ▸ old_retained G P q nonzero j
  · let j : Fin (addedCount G q nonzero) := ⟨i.val-P.count,by have := i.isLt; unfold count at this; omega⟩
    have hn : newLabel G P q nonzero j = i := Fin.ext (by dsimp [newLabel,j]; omega)
    rw [←hn] at hu
    have he := congrArg (fun z : TreeOccurrence (OI.K G) => z.2.leaves) (new_saved G P q nonzero j)
    change (trees G P q nonzero (newLabel G P q nonzero j)).leaves =
      (entry G q nonzero j).2.leaves at he
    rw [he] at hu
    have rootLeaf : u ∈ (tree G q nonzero).leaves :=
      FactorSaturation.stored_leaves_subset (FactorSaturation.slot_stored _ _) u hu
    obtain ⟨leaf,hleaf⟩ := RetainedCatalogue.leaves_cover (tree G q nonzero) u rootLeaf
    exact hleaf ▸ slot_retained G P q nonzero (FactorSaturation.leafSlot _ leaf)

theorem original_saved (i : Fin (OI.count G)) : ∃ j : Fin (count G P q nonzero),
    occurrence G P q nonzero j = (⟨⟨OI.arity G i.val,OI.publicTable G i⟩,OI.storedTrees G i⟩ : TreeOccurrence (OI.K G)) := by
  obtain ⟨j,hj⟩ := P.originalSaved i
  exact ⟨oldLabel G P q nonzero j,(old_saved G P q nonzero j).trans hj⟩
theorem equality_retained : (⟨2,binarySignature Signature.equality⟩ : AnySignature (OI.K G)) ∈ family G P q nonzero := by
  obtain ⟨i,hi⟩ := P.equality
  exact hi ▸ old_retained G P q nonzero i

/-- Generic exact-tree interpreter; the actual source proof and root field
signature are fixed before any stored slot is inspected. -/
def treeIndexPower (t : FactorTree q)
    (actual : Gadget.Realizes P.family .disequality q.2) (j : FactorSaturation.Slots t) :
    GeneralPowerExposure.PowerMacro P.table (FactorSaturation.slot t j).1.2 := by
  cases savedSlotSplit t j with
  | root he =>
    rw [←he]
    exact DeckDirect.directPower P.table (P.retainsIdentity G) actual
  | factor complement split =>
    exact Classical.choice (split.left_power_labelled P.table (P.retainsIdentity G) (by norm_num)
      (mixedSupport_of_identity P.family (P.retainsIdentity G)) nonzero actual)

/-- Every slot uses THIS q tree's actual composed split, with the SAME actual
source realization. The root is direct exponent one; factors are charged powers. -/
def indexPower (actual : Gadget.Realizes P.family .disequality q.2) (j : NewIndex G q nonzero) :
    GeneralPowerExposure.PowerMacro P.table (newOccurrence G q nonzero j).1.2 :=
  treeIndexPower G P q nonzero (tree G q nonzero) actual j

/-- The root macro consumes the SAME actual proof, with no second source
localization choice at the catalogue boundary. -/
def rootPower (actual : Gadget.Realizes P.family .disequality q.2) :
    GeneralPowerExposure.PowerMacro P.table q.2 :=
  DeckDirect.directPower P.table (P.retainsIdentity G) actual

/-- Full dependent identity transports the root's signature together with
its actual macro data. This includes graph, labels, exponent and scalar. -/
theorem root_indexPower (actual : Gadget.Realizes P.family .disequality q.2) :
    (⟨(newOccurrence G q nonzero (savedRootSlot (tree G q nonzero))).1,
      indexPower G P q nonzero actual (savedRootSlot (tree G q nonzero))⟩ :
      Sigma (fun u : AnySignature (OI.K G) => GeneralPowerExposure.PowerMacro P.table u.2)) =
      ⟨q,rootPower G P q actual⟩ := by
  have generic (t : FactorTree q) :
      (⟨(FactorSaturation.slot t (savedRootSlot t)).1,
        treeIndexPower G P q nonzero t actual (savedRootSlot t)⟩ :
        Sigma (fun u : AnySignature (OI.K G) => GeneralPowerExposure.PowerMacro P.table u.2)) =
        ⟨q,rootPower G P q actual⟩ := by
    cases t <;> rfl
  exact generic (tree G q nonzero)

def newPower (actual : Gadget.Realizes P.family .disequality q.2) (j : Fin (addedCount G q nonzero)) :
    GeneralPowerExposure.PowerMacro P.table (entry G q nonzero j).1.2 :=
  indexPower G P q nonzero actual (enumerate G q nonzero j)

abbrev ToOriginalProgramme := PhysicalProgramme
  (RawClosedNetwork.validatedEncoding (count G P q nonzero) 1 (arity G P q nonzero)) (OI.presentation G).encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  (OriginalLCodec.value (table G P q nonzero)) (OriginalForestSource.value G)
abbrev FromOriginalProgramme := PhysicalProgramme
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  (RawClosedNetwork.validatedEncoding (count G P q nonzero) 1 (arity G P q nonzero)) (OI.presentation G).encoding
  (OriginalForestSource.value G) (OriginalLCodec.value (table G P q nonzero))

def withPhysical (positive : 0 < q.1) (toOriginal : ToOriginalProgramme G P q nonzero)
    (fromOriginal : FromOriginalProgramme G P q nonzero) : Palette G where
  count := count G P q nonzero
  arity := arity G P q nonzero
  table := table G P q nonzero
  positive := RetainedFactorCatalogue.positive G P q nonzero positive
  nonzero := table_nonzero G P q nonzero
  trees := trees G P q nonzero
  leavesRetained := leaves_retained G P q nonzero
  originalSaved := original_saved G P q nonzero
  equality := equality_retained G P q nonzero
  toOriginal := toOriginal
  fromOriginal := fromOriginal

end Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedFactorCatalogue
