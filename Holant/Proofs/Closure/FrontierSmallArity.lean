import Holant.Proofs.Closure.FrontierCurrentClosure
import Holant.Proofs.Closure.ClosureSmallArityScan
import Holant.Proofs.Closure.ClosureFactorTreeFieldMap


noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierSmallArity
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FrontierCommonPresentation CurrentFrontierClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

def atIndex (P : Palette G) (i : Fin (Fintype.card (CurrentOccurrences.Id G P))) :
    CurrentOccurrences.Id G P := (Fintype.equivFin (CurrentOccurrences.Id G P)).symm i

theorem atIndex_injective (P : Palette G) : Function.Injective (atIndex G P) :=
  (Fintype.equivFin (CurrentOccurrences.Id G P)).symm.injective

def firstLargeIndex (P : Palette G) : Option (Fin (Fintype.card (CurrentOccurrences.Id G P))) :=
  ClosureSmallArityScan.firstLarge _ (fun i => (CurrentOccurrences.savedLeaf G P (atIndex G P i)).1.1)

def scan (P : Palette G) : Option (CurrentOccurrences.Id G P) :=
  (firstLargeIndex G P).map (atIndex G P)

/-- The returned position is literally the first successful finRange.find?,
not an equal-valued leaf recovered through set membership. -/
theorem firstLargeIndex_actual (P : Palette G) : firstLargeIndex G P =
    (List.finRange (Fintype.card (CurrentOccurrences.Id G P))).find?
      (fun i => decide (3 ≤ (CurrentOccurrences.savedLeaf G P (atIndex G P i)).1.1)) := rfl

theorem scan_sound (P : Palette G) (o : CurrentOccurrences.Id G P) (h : scan G P = some o) :
    3 ≤ (CurrentOccurrences.savedLeaf G P o).1.1 := by
  cases hi : firstLargeIndex G P with
  | none => simp [scan,hi] at h
  | some i =>
      have he : atIndex G P i = o := by simpa [scan,hi] using h
      subst o
      exact ClosureSmallArityScan.firstLarge_sound _ _ i hi

theorem scan_none_iff (P : Palette G) : scan G P = none ↔
    ∀ o : CurrentOccurrences.Id G P, (CurrentOccurrences.savedLeaf G P o).1.1 ≤ 2 := by
  have hm : scan G P = none ↔ firstLargeIndex G P = none := by
    cases hi : firstLargeIndex G P <;> simp [scan,hi]
  rw [hm,firstLargeIndex,ClosureSmallArityScan.firstLarge_none_iff]
  constructor
  · intro h o
    simpa only [atIndex,Equiv.symm_apply_apply] using h ((Fintype.equivFin (CurrentOccurrences.Id G P)) o)
  · intro h i
    exact h (atIndex G P i)

/-- Value membership is used ONLY to prove an all-leaf bound. The selected
higher occurrence in scan_sound never passes through this value-level choice. -/
theorem all_saved_leaves_small (P : Palette G) (empty : scan G P = none)
    (i : Fin P.count) : ∀ f ∈ (P.trees i).leaves, f.1 = 1 ∨ f.1 = 2 := by
  intro f hf
  obtain ⟨p,hp⟩ := Occurrences.leaf_address_complete (P.trees i) f hf
  have hi := (scan_none_iff G P).mp empty (⟨i,p⟩ : CurrentOccurrences.Id G P)
  have lo := CurrentOccurrences.savedLeaf_positive G P (⟨i,p⟩ : CurrentOccurrences.Id G P)
  change (Occurrences.leaf (P.trees i) p).1.1 ≤ 2 at hi
  change 0 < (Occurrences.leaf (P.trees i) p).1.1 at lo
  rw [hp] at hi lo
  omega

/-- The all-small branch structurally maps the GIVEN saved trees, retaining
all split scales and ordered ports, then applies the forward native K basis. -/
theorem small_native_tractX (P : Palette G) (empty : scan G P = none) :
    TractX (familyAction sourceKBasis (currentFamily G P)) := by
  refine ⟨((currentFamily_finite G P).image _).subset (fun _ h => h.1),Or.inl ?_⟩
  rintro g ⟨⟨f,hf,rfl⟩,_pos,_nonzero⟩
  rcases hf with ⟨q,⟨i,rfl⟩,rfl⟩
  let phi := (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G).toRingHom
  have smallMapped : ∀ h ∈ (ClosureFactorTreeFieldMap.tree phi (P.trees i)).leaves,
      h.1 = 1 ∨ h.1 = 2 := by
    intro h hh
    rw [ClosureFactorTreeFieldMap.leaves] at hh
    obtain ⟨old,hold,rfl⟩ := Multiset.mem_map.mp hh
    exact all_saved_leaves_small G P empty i old hold
  have closure := ClosureSmallArity.small_tree (ClosureFactorTreeFieldMap.tree phi (P.trees i)) smallMapped
  exact Or.inr (Signature.TensorClosure.map_action sourceKBasis.matrix (fun _ _ h => h) closure)

structure Large (P : Palette G) where
  id : CurrentOccurrences.Id G P
  selected : scan G P = some id
  nonbinary : 3 ≤ (CurrentOccurrences.savedLeaf G P id).1.1
  domain : CurrentOccurrences.Domain G P id
  domainExact : domain = CurrentOccurrences.domain G P id

/-- The actual scanned position reconstructs the exact returned root/path ID. -/
theorem Large.scanned_index {P : Palette G} (d : Large G P) :
    ∃ i : Fin (Fintype.card (CurrentOccurrences.Id G P)),
      firstLargeIndex G P = some i ∧ atIndex G P i = d.id := by
  cases hi : firstLargeIndex G P with
  | none => have he := d.selected; simp [scan,hi] at he
  | some i => exact ⟨i,rfl,by simpa [scan,hi] using d.selected⟩

/-- Scanning is not preparation or local rigidity; the exact local domain
keeps its pending marker until a genuine applicable theorem is installed. -/
theorem Large.domain_pending {P : Palette G} (d : Large G P) :
    d.domain.preparation = Frontier.Preparation.pending := by
  rw [d.domainExact]
  exact CurrentOccurrences.domain_unprepared G P d.id

abbrev Large.toOriginal {P : Palette G} (d : Large G P) := d.domain.toOriginal G
abbrev Large.fromOriginal {P : Palette G} (d : Large G P) := d.domain.fromOriginal G

theorem Large.toOriginal_same_machine {P : Palette G} (d : Large G P) :
    d.toOriginal.controlled.reduction.machine = P.toOriginal.controlled.reduction.machine := rfl

theorem Large.fromOriginal_same_machine {P : Palette G} (d : Large G P) :
    d.fromOriginal.controlled.reduction.machine = P.fromOriginal.controlled.reduction.machine := rfl

/-- A scanned higher leaf supports existence of an actual family minimum;
its own arity is not labelled minimum merely because it was scanned first. -/
def Large.minimum {P : Palette G} (d : Large G P) : MinimumCore P.family :=
  Classical.choice (exists_minimumCore P.family ⟨_,CurrentOccurrences.savedLeaf_retained G P d.id,
    CurrentOccurrences.savedLeaf_prime G P d.id,d.nonbinary⟩)

inductive Result (P : Palette G) : Type
  | large (data : Large G P)
  | small (empty : scan G P = none)
      (criterion : TractX (familyAction sourceKBasis (currentFamily G P)))

/-- Closed actual palette scan. No caller arity policy or closure solver. -/
def inspect (P : Palette G) : Result G P := by
  cases h : scan G P with
  | none => exact .small h (small_native_tractX G P h)
  | some o => exact .large ⟨o,h,scan_sound G P o h,CurrentOccurrences.domain G P o,rfl⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierSmallArity
end
