import Holant.Proofs.Reductions.FactorSaturation.Reconstruction
import Holant.Proofs.Reductions.GeneralExtraction.RetainedPairReduction


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FactorSaturation
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
variable {K : Type} [Field K] {s : ℕ}
variable (roots : Fin s → AnySignature K) (hn : ∀ i, (roots i).2 ≠ 0)

abbrev addedCount := Fintype.card (NewNode roots hn)
def enumerate : Fin (addedCount roots hn) ≃ NewNode roots hn := (Fintype.equivFin _).symm
def entry (j : Fin (addedCount roots hn)) : AnySignature K := (newNode roots hn (enumerate roots hn j)).1

def lookup (i : ℕ) : AnySignature K :=
  if hi : i < s then roots ⟨i,hi⟩ else
  if hj : i-s < addedCount roots hn then entry roots hn ⟨i-s,hj⟩ else ⟨0,0⟩
def arity (i : ℕ) : ℕ := (lookup roots hn i).1
def «prefix» (n : ℕ) (i : Fin (s+n)) : Signature K (arity roots hn i.val) := (lookup roots hn i.val).2
def next (n : ℕ) : Signature K (arity roots hn (s+n)) := (lookup roots hn (s+n)).2
abbrev original := «prefix» roots hn 0
abbrev augmented := «prefix» roots hn (addedCount roots hn)

@[simp] theorem lookup_old (i : Fin s) : lookup roots hn i.val = roots i := by
  simp [lookup, i.isLt]
@[simp] theorem lookup_new (j : Fin (addedCount roots hn)) : lookup roots hn (s+j.val) = entry roots hn j := by
  unfold lookup
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1
  apply Fin.ext
  change s + j.val - s = j.val
  omega

theorem original_family :
    Set.range (fun i : Fin s => (⟨arity roots hn i.val, original roots hn i⟩ : AnySignature K)) =
      Set.range roots := by
  congr 1
  funext i
  exact lookup_old roots hn i

theorem prefix_extension (n : ℕ) :
    RetainedPairReduction.extended («prefix» roots hn n) (next roots hn n) = «prefix» roots hn (n+1) := by
  funext i x
  by_cases hi : i.val < s+n
  · have h := congrFun (GeneralOriginalQuery.source_old («prefix» roots hn n) (next roots hn n) ⟨i.val,hi⟩) x
    exact h
  · have he : i = ⟨s+n, by omega⟩ := Fin.ext (by change i.val = s+n; omega)
    revert x
    rw [he]
    intro x
    exact congrFun (GeneralOriginalQuery.source_new («prefix» roots hn n) (next roots hn n)) x

theorem augmented_family :
    Set.range (fun i => (⟨arity roots hn i.val, augmented roots hn i⟩ : AnySignature K)) =
      Set.range roots ∪ Set.range (entry roots hn) := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val < s
    · exact Or.inl ⟨⟨i.val,hi⟩, (lookup_old roots hn ⟨i.val,hi⟩).symm⟩
    · let j : Fin (addedCount roots hn) := ⟨i.val-s,by omega⟩
      have he : i.val = s+j.val := by dsimp [j]; omega
      exact Or.inr ⟨j, by change entry roots hn j = lookup roots hn i.val; rw [he,lookup_new]⟩
  · rintro (⟨i,rfl⟩ | ⟨j,rfl⟩)
    · exact ⟨⟨i.val,by omega⟩,lookup_old roots hn i⟩
    · exact ⟨⟨s+j.val,by omega⟩,lookup_new roots hn j⟩

theorem entry_nonzero (j : Fin (addedCount roots hn)) : (entry roots hn j).2 ≠ 0 := new_nonzero roots hn _
theorem entry_positive (hp : ∀ i, 0 < (roots i).1) (j : Fin (addedCount roots hn)) :
    0 < (entry roots hn j).1 := new_positive roots hn hp _

theorem slot_root_or_proper {f : AnySignature K} (t : FactorTree f) (w : Slots t) :
    (slot t w).1 = f ∨ ∃ u : ProperSlots t, slot t (properSlot t u) = slot t w := by
  cases t with
  | leaf f p => exact Or.inl rfl
  | split q l r =>
      rcases w with u | w
      · exact Or.inl rfl
      · exact Or.inr ⟨w, rfl⟩

theorem all_slots_retained (i : Fin s) (v : Slots (tree roots hn i)) :
    (slot (tree roots hn i) v).1 ∈ Set.range roots ∪ Set.range (entry roots hn) := by
  rcases slot_root_or_proper (tree roots hn i) v with h | ⟨w, hw⟩
  · exact Or.inl ⟨i, h.symm⟩
  · let a : NewNode roots hn := ⟨i, w⟩
    refine Or.inr ⟨(enumerate roots hn).symm a, ?_⟩
    unfold entry
    rw [Equiv.apply_symm_apply]
    exact congrArg Sigma.fst hw

theorem leaves_retained (i : Fin s) (a : AnySignature K) (ha : a ∈ (tree roots hn i).leaves) :
    a ∈ Set.range roots ∪ Set.range (entry roots hn) := by
  have enum_leaf {f : AnySignature K} (t : FactorTree f) :
      ∀ a ∈ t.leaves, ∃ v : Slots t, (slot t v).1 = a := by
    induction t with
    | leaf f p => intro a ha; exact ⟨(), (Multiset.mem_singleton.mp ha).symm⟩
    | split q l r il ir =>
        intro a ha
        rcases Multiset.mem_add.mp ha with ha | ha
        · obtain ⟨v,hv⟩ := il a ha; exact ⟨.inr (.inl v),hv⟩
        · obtain ⟨v,hv⟩ := ir a ha; exact ⟨.inr (.inr v),hv⟩
  obtain ⟨v,rfl⟩ := enum_leaf _ a ha
  exact all_slots_retained roots hn i v

theorem stored_leaves_subset {u t : TreeOccurrence K}
    (h : OccurrenceSchedule.StoredSubtree u t) : ∀ a ∈ u.2.leaves, a ∈ t.2.leaves := by
  induction h with
  | root => exact fun _ ha => ha
  | left q l r h ih => exact fun a ha => Multiset.mem_add.mpr (Or.inl (ih a ha))
  | right q l r h ih => exact fun a ha => Multiset.mem_add.mpr (Or.inr (ih a ha))

/-- Saturation is proved for the CONSTRUCTED forest, including composites;
the chosen subtree supplies each intermediate's own prime decomposition. -/
theorem saturated : FactorSaturated
    (Set.range (fun i => (⟨arity roots hn i.val, augmented roots hn i⟩ : AnySignature K))) := by
  rw [augmented_family]
  intro f hf _
  rcases hf with ⟨i,rfl⟩ | ⟨j,rfl⟩
  · exact ⟨tree roots hn i, leaves_retained roots hn i⟩
  · let u := enumerate roots hn j
    refine ⟨(newNode roots hn u).2, ?_⟩
    intro a ha
    exact leaves_retained roots hn u.1 a
      (stored_leaves_subset (slot_stored (tree roots hn u.1) (properSlot _ u.2)) a ha)

theorem finite_augmented :
    (Set.range (fun i => (⟨arity roots hn i.val, augmented roots hn i⟩ : AnySignature K))).Finite :=
  Set.finite_range _

end Holant.LocalDrafts.Hardness.FactorSaturation
