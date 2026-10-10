import Holant.Proofs.Closure.OccurrenceCurrent
import Holant.Proofs.Closure.OccurrenceBatch

/-! Exact old/new occurrence partition of one actual nonminimum retained batch.
Old saved root-plus-address IDs copy injectively, while every genuinely new
saved prime occurrence has arity strictly below the selected m+2 occurrence.
Values, projective classes and equal saved trees are never deduplicated. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklistPartition
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
open Holant.LocalDrafts.Hardness
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (retained : (⟨m+2,f⟩ : AnySignature (OI.K G)) ∈ P.family) (hm : 2 ≤ m)

abbrev palette : Palette G := OccurrenceBatch.palette G P torsion f retained hm

/-- This is the actual old-first physical catalogue injection. -/
def copyId (o : CurrentOccurrences.Id G P) : CurrentOccurrences.Id G (palette G P torsion f retained hm) :=
  ⟨RetainedCatalogue.oldLabel G P torsion f o.1,
    Occurrences.transportAddress (RetainedCatalogue.old_saved G P torsion f o.1).symm o.2⟩

theorem copyId_leaf (o : CurrentOccurrences.Id G P) :
    CurrentOccurrences.savedLeaf G (palette G P torsion f retained hm)
      (copyId G P torsion f retained hm o) = CurrentOccurrences.savedLeaf G P o :=
  Occurrences.transportAddress_leaf (RetainedCatalogue.old_saved G P torsion f o.1).symm o.2

theorem copyId_root_val (o : CurrentOccurrences.Id G P) :
    (copyId G P torsion f retained hm o).1.val = o.1.val := rfl

@[simp] theorem copyId_arity (o : CurrentOccurrences.Id G P) :
    (CurrentOccurrences.savedLeaf G (palette G P torsion f retained hm)
      (copyId G P torsion f retained hm o)).1.1 = (CurrentOccurrences.savedLeaf G P o).1.1 :=
  congrArg (fun u : TreeOccurrence (OI.K G) => u.1.1) (copyId_leaf G P torsion f retained hm o)

theorem copyId_injective : Function.Injective (copyId G P torsion f retained hm) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ he
  have hi : i = j := Fin.ext (congrArg (fun o => o.1.val) he)
  subst j
  have hp : Occurrences.transportAddress (RetainedCatalogue.old_saved G P torsion f i).symm p =
      Occurrences.transportAddress (RetainedCatalogue.old_saved G P torsion f i).symm q :=
    @sigma_mk_injective (Fin (palette G P torsion f retained hm).count)
      (fun k => Occurrences.Address ((palette G P torsion f retained hm).trees k))
      (RetainedCatalogue.oldLabel G P torsion f i) _ _ he
  exact Sigma.ext rfl (heq_of_eq
    (Occurrences.transportAddress_injective (RetainedCatalogue.old_saved G P torsion f i).symm hp))

def copyEmbedding : CurrentOccurrences.Id G P ↪ CurrentOccurrences.Id G (palette G P torsion f retained hm) :=
  ⟨copyId G P torsion f retained hm, copyId_injective G P torsion f retained hm⟩

def oldIds : Finset (CurrentOccurrences.Id G (palette G P torsion f retained hm)) :=
  Finset.univ.map (copyEmbedding G P torsion f retained hm)

theorem map_oldIds : Finset.univ.map (copyEmbedding G P torsion f retained hm) =
    oldIds G P torsion f retained hm := rfl

def newIds : Finset (CurrentOccurrences.Id G (palette G P torsion f retained hm)) :=
  Finset.univ.filter (fun o => P.count ≤ o.1.val)

theorem mem_newIds (o : CurrentOccurrences.Id G (palette G P torsion f retained hm)) :
    o ∈ newIds G P torsion f retained hm ↔ P.count ≤ o.1.val := by
  simp [newIds]

private theorem transport_inverse {L : Type*} [Field L] {u v : TreeOccurrence L}
    (h : u = v) (p : Occurrences.Address u.2) :
    Occurrences.transportAddress h.symm (Occurrences.transportAddress h p) = p := by
  cases h
  rfl

theorem mem_oldIds (o : CurrentOccurrences.Id G (palette G P torsion f retained hm)) :
    o ∈ oldIds G P torsion f retained hm ↔ o.1.val < P.count := by
  constructor
  · intro ho
    obtain ⟨p, _, he⟩ := Finset.mem_map.mp ho
    rw [← he]
    exact p.1.isLt
  · rcases o with ⟨j,p⟩
    intro hj
    have old : ∃ i : Fin P.count, RetainedCatalogue.oldLabel G P torsion f i = j :=
      ⟨⟨j.val,hj⟩,Fin.ext rfl⟩
    obtain ⟨i,rfl⟩ := old
    let q := Occurrences.transportAddress (RetainedCatalogue.old_saved G P torsion f i) p
    apply Finset.mem_map.mpr
    refine ⟨⟨i,q⟩, Finset.mem_univ _, ?_⟩
    change (⟨RetainedCatalogue.oldLabel G P torsion f i,
      Occurrences.transportAddress (RetainedCatalogue.old_saved G P torsion f i).symm q⟩ :
        CurrentOccurrences.Id G (palette G P torsion f retained hm)) =
      ⟨RetainedCatalogue.oldLabel G P torsion f i,p⟩
    exact congrArg (fun p => (⟨RetainedCatalogue.oldLabel G P torsion f i,p⟩ :
      CurrentOccurrences.Id G (palette G P torsion f retained hm)))
      (transport_inverse (RetainedCatalogue.old_saved G P torsion f i) p)

theorem old_new_disjoint :
    Disjoint (oldIds G P torsion f retained hm) (newIds G P torsion f retained hm) := by
  apply Finset.disjoint_left.mpr
  intro o ho hn
  have hold := (mem_oldIds G P torsion f retained hm o).mp ho
  have hnew := (mem_newIds G P torsion f retained hm o).mp hn
  omega

theorem partition : oldIds G P torsion f retained hm ∪ newIds G P torsion f retained hm = Finset.univ := by
  apply Finset.ext
  intro o
  simp only [Finset.mem_union, mem_oldIds, mem_newIds, Finset.mem_univ, iff_true]
  omega

theorem copy_disjoint_new : Disjoint
    (Finset.univ.map (copyEmbedding G P torsion f retained hm)) (newIds G P torsion f retained hm) :=
  old_new_disjoint G P torsion f retained hm

theorem copied_new_partition :
    Finset.univ.map (copyEmbedding G P torsion f retained hm) ∪ newIds G P torsion f retained hm =
      Finset.univ := partition G P torsion f retained hm

theorem oldIds_card : (oldIds G P torsion f retained hm).card = Fintype.card (CurrentOccurrences.Id G P) := by
  simp [oldIds]

include hm in
theorem fullRoot_arity_lt (k : RetainedCatalogue.Key G P torsion f) :
    (RetainedCatalogue.Root G P torsion f k).1.1 < m+2 := by
  cases k with
  | inl group => change 2 < m+2; omega
  | inr raw => change m < m+2; omega

include hm in
theorem newOccurrence_arity_lt (x : RetainedCatalogue.NewIndex G P torsion f) :
    (RetainedCatalogue.newOccurrence G P torsion f x).1.1 < m+2 := by
  cases x with
  | inl k => exact fullRoot_arity_lt G P torsion f hm k
  | inr x =>
      exact ((RetainedCatalogue.Root G P torsion f x.1).2.leaf_arity_le _
        (FactorSaturation.leaf_mem _ x.2)).trans_lt (fullRoot_arity_lt G P torsion f hm x.1)

/-- A genuinely new dense label has one of the exact new saved trees. -/
theorem new_root_arity_lt (i : Fin (palette G P torsion f retained hm).count)
    (new : P.count ≤ i.val) : (palette G P torsion f retained hm).arity i.val < m+2 := by
  have isLt : i.val < P.count + RetainedCatalogue.addedCount G P torsion f := i.isLt
  let j : Fin (RetainedCatalogue.addedCount G P torsion f) := ⟨i.val-P.count,by omega⟩
  have hi : RetainedCatalogue.newLabel G P torsion f j = i := by
    apply Fin.ext
    dsimp [RetainedCatalogue.newLabel,j]
    omega
  have hroot := congrArg (fun u : TreeOccurrence (OI.K G) => u.1.1)
    (RetainedCatalogue.new_saved G P torsion f j)
  have bound := newOccurrence_arity_lt G P torsion f hm (RetainedCatalogue.enumerate G P torsion f j)
  change (RetainedCatalogue.entry G P torsion f j).1.1 < m+2 at bound
  rw [← hi]
  exact hroot.le.trans_lt bound

/-- Every newly installed saved prime occurrence has strictly lower arity
than the selected m+2 prime, including leaves of a new composite deck root. -/
theorem newIds_lower (o : CurrentOccurrences.Id G (palette G P torsion f retained hm))
    (ho : o ∈ newIds G P torsion f retained hm) :
    (CurrentOccurrences.savedLeaf G (palette G P torsion f retained hm) o).1.1 < m+2 :=
  ((palette G P torsion f retained hm).trees o.1).leaf_arity_le _
      (Occurrences.leaf_mem _ o.2) |>.trans_lt
    (new_root_arity_lt G P torsion f retained hm o.1 ((mem_newIds G P torsion f retained hm o).mp ho))

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklistPartition
end
