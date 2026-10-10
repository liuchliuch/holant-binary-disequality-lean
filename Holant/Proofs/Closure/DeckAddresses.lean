import Holant.Proofs.Closure.DeckKernel
import Holant.Proofs.Reductions.FactorSaturation.Reconstruction

/-! Reconstructed canonical leaf addresses. Each leaf index is an occurrence;
paths distinguish equal values in different branches. UNVERIFIED recovery. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
variable {L : Type} [Field L]

theorem savedLeafSlot_injective {f : AnySignature L} (t : FactorTree f) :
    Function.Injective (FactorSaturation.leafSlot t) := by
  induction t with
  | leaf => exact Function.injective_id
  | split sp l r il ir =>
    intro a b h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (il (Sum.inl.inj (Sum.inr.inj h)))
      | inr b => cases h
    | inr a => cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (ir (Sum.inr.inj (Sum.inr.inj h)))

def savedLeafPath {f : AnySignature L} (t : FactorTree f) (j : FactorSaturation.Leaves t) : List Bool :=
  FactorSaturation.path t (FactorSaturation.leafSlot t j)

theorem savedLeafPath_injective {f : AnySignature L} (t : FactorTree f) :
    Function.Injective (savedLeafPath t) :=
  (FactorSaturation.path_injective t).comp (savedLeafSlot_injective t)

def indexedLeafOccurrences {f : AnySignature L} (t : FactorTree f) :
    Multiset (List Bool × TreeOccurrence L) :=
  (Finset.univ : Finset (FactorSaturation.Leaves t)).val.map
    (fun j => (savedLeafPath t j,FactorSaturation.slot t (FactorSaturation.leafSlot t j)))

@[simp] theorem indexedLeafOccurrences_leaf (f : AnySignature L) (hp : Prime f) :
    indexedLeafOccurrences (FactorTree.leaf f hp) = {([],⟨f,.leaf f hp⟩)} := by
  simp [indexedLeafOccurrences,FactorSaturation.Leaves,FactorSaturation.leavesFintype,
    savedLeafPath,FactorSaturation.leafSlot,FactorSaturation.path,FactorSaturation.slot]

theorem indexedLeafOccurrences_split {f a b : AnySignature L} (sp : ProperSplit f a b)
    (l : FactorTree a) (r : FactorTree b) :
    indexedLeafOccurrences (.split sp l r) =
      (indexedLeafOccurrences l).map (fun u => (false::u.1,u.2)) +
      (indexedLeafOccurrences r).map (fun u => (true::u.1,u.2)) := by
  unfold indexedLeafOccurrences
  change (Finset.univ : Finset (FactorSaturation.Leaves l ⊕ FactorSaturation.Leaves r)).val.map _ = _
  rw [← Finset.univ_disjSum_univ,Finset.val_disjSum,Multiset.disjSum,
    Multiset.map_add,Multiset.map_map,Multiset.map_map]
  simp only [Multiset.map_map]
  rfl

theorem leafOccurrences_indexed {f : AnySignature L} (t : FactorTree f) :
    (indexedLeafOccurrences t).map Prod.snd = leafOccurrences t := by
  induction t with
  | leaf f hp => simp only [indexedLeafOccurrences_leaf,Multiset.map_singleton,leafOccurrences]
  | split sp l r il ir =>
    rw [indexedLeafOccurrences_split,Multiset.map_add,Multiset.map_map,Multiset.map_map]
    change (indexedLeafOccurrences l).map Prod.snd + (indexedLeafOccurrences r).map Prod.snd = _
    rw [il,ir]
    rfl

theorem indexedLeafOccurrences_values {f : AnySignature L} (t : FactorTree f) :
    (indexedLeafOccurrences t).map (fun u => u.2.1) = t.leaves := by
  calc
    (indexedLeafOccurrences t).map (fun u => u.2.1) =
        ((indexedLeafOccurrences t).map Prod.snd).map Sigma.fst :=
      (Multiset.map_map Sigma.fst Prod.snd (indexedLeafOccurrences t)).symm
    _ = t.leaves := by rw [leafOccurrences_indexed,leafOccurrences_values]

theorem savedLeafOccurrence_mem {f : AnySignature L} (t : FactorTree f)
    (j : FactorSaturation.Leaves t) :
    FactorSaturation.slot t (FactorSaturation.leafSlot t j) ∈ leafOccurrences t := by
  rw [← leafOccurrences_indexed,indexedLeafOccurrences]
  exact Multiset.mem_map.mpr ⟨_,Multiset.mem_map.mpr ⟨j,Finset.mem_univ j,rfl⟩,rfl⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2
