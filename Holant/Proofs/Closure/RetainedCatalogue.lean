import Holant.Proofs.Closure.DeckPhysical
import Holant.Proofs.Closure.DeckAddresses

/-! Reconstructed literal old-first retained catalogue. Every full root and
prime leaf occurrence has its own dense label. UNVERIFIED recovery bytes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedCatalogue
open scoped BigOperators
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))

abbrev Key := FullDeckIndex P.family torsion f
abbrev Root (k : Key G P torsion f) := fullDeckRoot P.family torsion f k
instance keyFintype : Fintype (Key G P torsion f) := by
  letI := completeGroup_finite P.family torsion
  exact Fintype.ofFinite _
abbrev NewIndex := Key G P torsion f ⊕
  (Σ k : Key G P torsion f, FactorSaturation.Leaves (Root G P torsion f k).2)
instance newIndexFintype : Fintype (NewIndex G P torsion f) := inferInstance

def newOccurrence : NewIndex G P torsion f → TreeOccurrence (OI.K G)
  | .inl k => Root G P torsion f k
  | .inr x => FactorSaturation.slot (Root G P torsion f x.1).2
      (FactorSaturation.leafSlot (Root G P torsion f x.1).2 x.2)

def addedCount : ℕ := Fintype.card (NewIndex G P torsion f)
def enumerate : Fin (addedCount G P torsion f) ≃ NewIndex G P torsion f :=
  (Fintype.equivFin _).symm
def entry (j : Fin (addedCount G P torsion f)) : TreeOccurrence (OI.K G) :=
  newOccurrence G P torsion f (enumerate G P torsion f j)
def count : ℕ := P.count + addedCount G P torsion f

def lookup (n : ℕ) : AnySignature (OI.K G) :=
  if h : n < P.count then ⟨P.arity n,P.table ⟨n,h⟩⟩
  else if h : n < count G P torsion f then (entry G P torsion f ⟨n-P.count,by
    unfold count at h; omega⟩).1 else ⟨0,0⟩
def arity (n : ℕ) : ℕ := (lookup G P torsion f n).1
def table (i : Fin (count G P torsion f)) : Signature (OI.K G) (arity G P torsion f i.val) :=
  (lookup G P torsion f i.val).2

@[simp] theorem lookup_old (i : Fin P.count) :
    lookup G P torsion f i.val = (⟨P.arity i.val,P.table i⟩ : AnySignature (OI.K G)) := by
  simp only [lookup,dif_pos i.isLt]
@[simp] theorem lookup_new (j : Fin (addedCount G P torsion f)) :
    lookup G P torsion f (P.count+j.val) = (entry G P torsion f j).1 := by
  have hn : ¬ P.count+j.val < P.count := by omega
  have hl : P.count+j.val < count G P torsion f := by unfold count; omega
  simp only [lookup,dif_neg hn,dif_pos hl,Nat.add_sub_cancel_left]

def transportTree {L : Type} [Field L] {u v : AnySignature L}
    (h : u=v) (t : FactorTree u) : FactorTree v := h ▸ t

theorem transportTree_saved {L : Type} [Field L] {u v : AnySignature L}
    (h : u=v) (t : FactorTree u) :
    (⟨v,transportTree h t⟩ : TreeOccurrence L) = ⟨u,t⟩ := by cases h; rfl

def trees (i : Fin (count G P torsion f)) :
    FactorTree (⟨arity G P torsion f i.val,table G P torsion f i⟩ : AnySignature (OI.K G)) :=
  if h : i.val < P.count then
    transportTree (lookup_old G P torsion f ⟨i.val,h⟩).symm (P.trees ⟨i.val,h⟩)
  else
    let j : Fin (addedCount G P torsion f) := ⟨i.val-P.count,by have := i.isLt; unfold count at this; omega⟩
    transportTree (by
      change (entry G P torsion f j).1 = lookup G P torsion f i.val
      have hn : i.val = P.count+j.val := by dsimp [j]; omega
      rw [hn]
      exact (lookup_new G P torsion f j).symm) (entry G P torsion f j).2

def occurrence (i : Fin (count G P torsion f)) : TreeOccurrence (OI.K G) :=
  ⟨⟨arity G P torsion f i.val,table G P torsion f i⟩,trees G P torsion f i⟩

def oldLabel (i : Fin P.count) : Fin (count G P torsion f) := ⟨i.val,by unfold count; omega⟩
def newLabel (j : Fin (addedCount G P torsion f)) : Fin (count G P torsion f) :=
  ⟨P.count+j.val,by unfold count; omega⟩
def deckLabel (k : Key G P torsion f) : Fin (count G P torsion f) :=
  newLabel G P torsion f ((enumerate G P torsion f).symm (.inl k))
def leafLabel (k : Key G P torsion f) (j : FactorSaturation.Leaves (Root G P torsion f k).2) :
    Fin (count G P torsion f) :=
  newLabel G P torsion f ((enumerate G P torsion f).symm (.inr ⟨k,j⟩))

@[simp] theorem old_saved (i : Fin P.count) :
    (⟨⟨arity G P torsion f (oldLabel G P torsion f i).val,
      table G P torsion f (oldLabel G P torsion f i)⟩,
      trees G P torsion f (oldLabel G P torsion f i)⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨P.arity i.val,P.table i⟩,P.trees i⟩ := by
  change (⟨lookup G P torsion f i.val,trees G P torsion f (oldLabel G P torsion f i)⟩ : TreeOccurrence _) = _
  simp only [trees,oldLabel,dif_pos i.isLt]
  exact transportTree_saved (L:=OI.K G) _ _

@[simp] theorem new_saved (j : Fin (addedCount G P torsion f)) :
    (⟨⟨arity G P torsion f (newLabel G P torsion f j).val,
      table G P torsion f (newLabel G P torsion f j)⟩,
      trees G P torsion f (newLabel G P torsion f j)⟩ : TreeOccurrence (OI.K G)) = entry G P torsion f j := by
  have hn : ¬ P.count+j.val < P.count := by omega
  change (⟨lookup G P torsion f (P.count+j.val),trees G P torsion f (newLabel G P torsion f j)⟩ : TreeOccurrence _) = _
  simp only [trees,newLabel,dif_neg hn]
  let jj : Fin (addedCount G P torsion f) :=
    ⟨P.count+j.val-P.count, by omega⟩
  have hj : jj = j := by apply Fin.ext; dsimp [jj]; omega
  trans entry G P torsion f jj
  · exact transportTree_saved (L:=OI.K G) _ _
  · exact congrArg (entry G P torsion f) hj

@[simp] theorem deck_saved (k : Key G P torsion f) :
    (⟨⟨arity G P torsion f (deckLabel G P torsion f k).val,
      table G P torsion f (deckLabel G P torsion f k)⟩,
      trees G P torsion f (deckLabel G P torsion f k)⟩ : TreeOccurrence (OI.K G)) = Root G P torsion f k := by
  unfold deckLabel
  rw [new_saved]
  simp only [entry,Equiv.apply_symm_apply,newOccurrence]

@[simp] theorem leaf_saved (k : Key G P torsion f)
    (j : FactorSaturation.Leaves (Root G P torsion f k).2) :
    (⟨⟨arity G P torsion f (leafLabel G P torsion f k j).val,
      table G P torsion f (leafLabel G P torsion f k j)⟩,
      trees G P torsion f (leafLabel G P torsion f k j)⟩ : TreeOccurrence (OI.K G)) =
      FactorSaturation.slot (Root G P torsion f k).2 (FactorSaturation.leafSlot (Root G P torsion f k).2 j) := by
  unfold leafLabel
  rw [new_saved]
  simp only [entry,Equiv.apply_symm_apply,newOccurrence]

theorem oldLabel_injective : Function.Injective (oldLabel G P torsion f) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin (count G P torsion f) => x.val) h
theorem newLabel_injective : Function.Injective (newLabel G P torsion f) := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  change P.count+i.val = P.count+j.val at he
  omega

theorem deckLabel_injective : Function.Injective (deckLabel G P torsion f) := by
  intro i j h
  exact Sum.inl.inj ((enumerate G P torsion f).symm.injective (newLabel_injective G P torsion f h))

theorem leafLabel_injective (k : Key G P torsion f) : Function.Injective (leafLabel G P torsion f k) := by
  intro i j h
  have hs := Sum.inr.inj ((enumerate G P torsion f).symm.injective (newLabel_injective G P torsion f h))
  exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2

theorem leaves_cover {L : Type} [Field L] {u : AnySignature L} (t : FactorTree u)
    (v : AnySignature L) (hv : v ∈ t.leaves) :
    ∃ j : FactorSaturation.Leaves t, FactorSaturation.leaf t j = v := by
  induction t with
  | leaf u hp => exact ⟨(),(Multiset.mem_singleton.mp hv).symm⟩
  | split sp l r il ir =>
    rcases Multiset.mem_add.mp hv with hl | hr
    · obtain ⟨j,hj⟩ := il hl; exact ⟨Sum.inl j,hj⟩
    · obtain ⟨j,hj⟩ := ir hr; exact ⟨Sum.inr j,hj⟩

theorem leaf_tree_singleton {L : Type} [Field L] {u : AnySignature L} (t : FactorTree u)
    (j : FactorSaturation.Leaves t) :
    (FactorSaturation.slot t (FactorSaturation.leafSlot t j)).2.leaves =
      {(FactorSaturation.slot t (FactorSaturation.leafSlot t j)).1} := by
  induction t with
  | leaf => rfl
  | split sp l r il ir => cases j with
    | inl j => exact il j
    | inr j => exact ir j

theorem leaf_occurrences_cover {L : Type} [Field L] {u : AnySignature L} (t : FactorTree u)
    (v : TreeOccurrence L) (hv : v ∈ OccurrenceSchedule.leafOccurrences t) :
    ∃ j : FactorSaturation.Leaves t, FactorSaturation.slot t (FactorSaturation.leafSlot t j) = v := by
  rw [←leafOccurrences_indexed,indexedLeafOccurrences] at hv
  obtain ⟨p,hp,he⟩ := Multiset.mem_map.mp hv
  obtain ⟨j,_,hj⟩ := Multiset.mem_map.mp hp
  exact ⟨j,(congrArg Prod.snd hj).trans he⟩

theorem leaf_occurrence_saved (k : Key G P torsion f) (u : TreeOccurrence (OI.K G))
    (hu : u ∈ OccurrenceSchedule.leafOccurrences (Root G P torsion f k).2) :
    ∃ i : Fin (count G P torsion f), occurrence G P torsion f i = u := by
  obtain ⟨j,hj⟩ := leaf_occurrences_cover (Root G P torsion f k).2 u hu
  exact ⟨leafLabel G P torsion f k j,(leaf_saved G P torsion f k j).trans hj⟩

theorem leaf_occurrence_card {L : Type} [Field L] {u : AnySignature L} (t : FactorTree u) :
    Fintype.card (FactorSaturation.Leaves t) = (OccurrenceSchedule.leafOccurrences t).card := by
  rw [←leafOccurrences_indexed]
  simp only [Multiset.card_map,indexedLeafOccurrences,Finset.card_val,Finset.card_univ]

theorem added_count_occurrences : addedCount G P torsion f = Fintype.card (Key G P torsion f) +
    ∑ k : Key G P torsion f, (OccurrenceSchedule.leafOccurrences (Root G P torsion f k).2).card := by
  simp only [addedCount,NewIndex,newIndexFintype,Fintype.card_sum,Fintype.card_sigma]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => leaf_occurrence_card _)

def family : SignatureFamily (OI.K G) :=
  Set.range (fun i : Fin (count G P torsion f) => (⟨arity G P torsion f i.val,table G P torsion f i⟩ : AnySignature (OI.K G)))

theorem newOccurrence_mem (x : NewIndex G P torsion f) :
    (newOccurrence G P torsion f x).1 ∈ fullRetainedDeck P.family torsion f := by
  classical
  cases x with
  | inl k => exact retainBatch_root P.family _ _ (mem_fullDeckUniverse P.family torsion f k)
  | inr x =>
    exact fullRetainedDeck_leaf P.family torsion f x.1 _
      (FactorSaturation.leaf_mem (Root G P torsion f x.1).2 x.2)

theorem family_exact : family G P torsion f = fullRetainedDeck P.family torsion f := by
  classical
  ext u
  constructor
  · rintro ⟨i,rfl⟩
    change lookup G P torsion f i.val ∈ fullRetainedDeck P.family torsion f
    by_cases hi : i.val < P.count
    · rw [lookup_old G P torsion f ⟨i.val,hi⟩]
      exact fullRetainedDeck_retains P.family torsion f ⟨⟨i.val,hi⟩,rfl⟩
    · let j : Fin (addedCount G P torsion f) := ⟨i.val-P.count,by have := i.isLt; unfold count at this; omega⟩
      have hn : i.val = P.count+j.val := by dsimp [j]; omega
      rw [hn,lookup_new]
      exact newOccurrence_mem G P torsion f (enumerate G P torsion f j)
  · rintro (hu | hu)
    · obtain ⟨i,rfl⟩ := hu
      exact ⟨oldLabel G P torsion f i,congrArg Sigma.fst (old_saved G P torsion f i)⟩
    · obtain ⟨k,hk,he | hl⟩ := (mem_batchCarrier _ _ u).mp hu
      · exact ⟨deckLabel G P torsion f k,(congrArg Sigma.fst (deck_saved G P torsion f k)).trans he.symm⟩
      · obtain ⟨j,hj⟩ := leaves_cover (Root G P torsion f k).2 u hl
        exact ⟨leafLabel G P torsion f k j,(congrArg Sigma.fst (leaf_saved G P torsion f k j)).trans hj⟩

theorem root_positive (hm : 2 ≤ m) (k : Key G P torsion f) : 0 < (Root G P torsion f k).1.1 := by
  cases k <;> simp only [Root,fullDeckRoot] <;> omega

theorem newOccurrence_positive (hm : 2 ≤ m) (x : NewIndex G P torsion f) :
    0 < (newOccurrence G P torsion f x).1.1 := by
  cases x with
  | inl k => exact root_positive G P torsion f hm k
  | inr x =>
    exact FactorSaturation.stored_positive (FactorSaturation.slot_stored _ _)
      (root_positive G P torsion f hm x.1)

theorem newOccurrence_nonzero (x : NewIndex G P torsion f) :
    (newOccurrence G P torsion f x).1.2 ≠ 0 := by
  cases x with
  | inl k => exact fullDeckRoot_nonzero P.family torsion f k
  | inr x =>
    exact FactorSaturation.stored_nonzero (FactorSaturation.slot_stored _ _)
      (fullDeckRoot_nonzero P.family torsion f x.1)

theorem positive (hm : 2 ≤ m) (i : Fin (count G P torsion f)) : 0 < arity G P torsion f i.val := by
  by_cases hi : i.val < P.count
  · change 0 < (lookup G P torsion f i.val).1
    rw [lookup_old G P torsion f ⟨i.val,hi⟩]
    exact P.positive ⟨i.val,hi⟩
  · let j : Fin (addedCount G P torsion f) := ⟨i.val-P.count,by have := i.isLt; unfold count at this; omega⟩
    have hn : i.val = P.count+j.val := by dsimp [j]; omega
    change 0 < (lookup G P torsion f i.val).1
    rw [hn,lookup_new]
    exact newOccurrence_positive G P torsion f hm _

theorem nonzero (i : Fin (count G P torsion f)) : table G P torsion f i ≠ 0 := by
  change (lookup G P torsion f i.val).2 ≠ 0
  by_cases hi : i.val < P.count
  · have he := lookup_old G P torsion f ⟨i.val,hi⟩
    exact Eq.mpr (congrArg (fun u : AnySignature (OI.K G) => u.2 ≠ 0) he) (P.nonzero ⟨i.val,hi⟩)
  · let j : Fin (addedCount G P torsion f) := ⟨i.val-P.count,by have := i.isLt; unfold count at this; omega⟩
    have hn : i.val = P.count+j.val := by dsimp [j]; omega
    have he : lookup G P torsion f i.val = (entry G P torsion f j).1 := by
      rw [hn]
      exact lookup_new G P torsion f j
    exact Eq.mpr (congrArg (fun u : AnySignature (OI.K G) => u.2 ≠ 0) he)
      (newOccurrence_nonzero G P torsion f (enumerate G P torsion f j))

theorem leaves_retained (i : Fin (count G P torsion f)) (u : AnySignature (OI.K G))
    (hu : u ∈ (trees G P torsion f i).leaves) : u ∈ family G P torsion f := by
  rw [family_exact]
  by_cases hi : i.val < P.count
  · have hn : oldLabel G P torsion f ⟨i.val,hi⟩ = i := Fin.ext rfl
    rw [←hn] at hu
    have he := congrArg (fun z : TreeOccurrence (OI.K G) => z.2.leaves) (old_saved G P torsion f ⟨i.val,hi⟩)
    rw [he] at hu
    exact fullRetainedDeck_retains P.family torsion f (P.leavesRetained _ _ hu)
  · let j : Fin (addedCount G P torsion f) := ⟨i.val-P.count,by have := i.isLt; unfold count at this; omega⟩
    have hn : newLabel G P torsion f j = i := Fin.ext (by dsimp [newLabel,j]; omega)
    rw [←hn] at hu
    have he := congrArg (fun z : TreeOccurrence (OI.K G) => z.2.leaves) (new_saved G P torsion f j)
    rw [he] at hu
    change u ∈ (newOccurrence G P torsion f (enumerate G P torsion f j)).2.leaves at hu
    cases hx : enumerate G P torsion f j with
    | inl k =>
      rw [hx] at hu
      exact fullRetainedDeck_leaf P.family torsion f k u hu
    | inr x =>
      rw [hx] at hu
      have hl := leaf_tree_singleton (Root G P torsion f x.1).2 x.2
      simp only [newOccurrence,hl,Multiset.mem_singleton] at hu
      rw [hu]
      exact newOccurrence_mem G P torsion f (.inr x)

theorem original_saved (i : Fin (OI.count G)) : ∃ j : Fin (count G P torsion f),
    (⟨⟨arity G P torsion f j.val,table G P torsion f j⟩,trees G P torsion f j⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨OI.arity G i.val,OI.publicTable G i⟩,OI.storedTrees G i⟩ := by
  obtain ⟨j,hj⟩ := P.originalSaved i
  exact ⟨oldLabel G P torsion f j,(old_saved G P torsion f j).trans hj⟩

theorem equality_retained : (⟨2,binarySignature Signature.equality⟩ : AnySignature (OI.K G)) ∈ family G P torsion f := by
  rw [family_exact]
  exact fullRetainedDeck_retains P.family torsion f P.equality

def rootSlot (k : Key G P torsion f) := savedRootSlot (Root G P torsion f k).2
@[simp] theorem slot_rootSlot (k : Key G P torsion f) :
    FactorSaturation.slot (Root G P torsion f k).2 (rootSlot G P torsion f k) = Root G P torsion f k := savedRootSlot_value _

theorem stored_slot_cover (k : Key G P torsion f) (u : TreeOccurrence (OI.K G))
    (hu : OccurrenceSchedule.StoredSubtree u (Root G P torsion f k)) :
    ∃ j : FactorSaturation.Slots (Root G P torsion f k).2,
      FactorSaturation.slot (Root G P torsion f k).2 j = u := savedSlot_cover hu

def newIndexPower (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (x : NewIndex G P torsion f) : GeneralPowerExposure.PowerMacro P.table (newOccurrence G P torsion f x).1.2 :=
  match x with
  | .inl k => DeckDirect.directPower P.table (P.retainsIdentity G) (deckRootDirect G P torsion f core hcore k).realizes
  | .inr x => deckSlotPower G P torsion f core hcore x.1 (FactorSaturation.leafSlot (Root G P torsion f x.1).2 x.2)

def newPower (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (j : Fin (addedCount G P torsion f)) : GeneralPowerExposure.PowerMacro P.table (entry G P torsion f j).1.2 :=
  newIndexPower G P torsion f core hcore (enumerate G P torsion f j)

@[simp] theorem newIndexPower_leaf (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (k : Key G P torsion f) (j : FactorSaturation.Leaves (Root G P torsion f k).2) :
    newIndexPower G P torsion f core hcore (.inr ⟨k,j⟩) =
      deckSlotPower G P torsion f core hcore k (FactorSaturation.leafSlot (Root G P torsion f k).2 j) := rfl

abbrev ToOriginalProgramme := PhysicalProgramme
  (RawClosedNetwork.validatedEncoding (count G P torsion f) 1 (arity G P torsion f)) (OI.presentation G).encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  (OriginalLCodec.value (table G P torsion f)) (OriginalForestSource.value G)
abbrev FromOriginalProgramme := PhysicalProgramme
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  (RawClosedNetwork.validatedEncoding (count G P torsion f) 1 (arity G P torsion f)) (OI.presentation G).encoding
  (OriginalForestSource.value G) (OriginalLCodec.value (table G P torsion f))

def withPhysical (hm : 2 ≤ m) (toOriginal : ToOriginalProgramme G P torsion f)
    (fromOriginal : FromOriginalProgramme G P torsion f) : Palette G where
  count := count G P torsion f
  arity := arity G P torsion f
  table := table G P torsion f
  positive := positive G P torsion f hm
  nonzero := nonzero G P torsion f
  trees := trees G P torsion f
  leavesRetained := leaves_retained G P torsion f
  originalSaved := original_saved G P torsion f
  equality := equality_retained G P torsion f
  toOriginal := toOriginal
  fromOriginal := fromOriginal

end Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedCatalogue
