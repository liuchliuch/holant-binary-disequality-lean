import Holant.Proofs.Reductions.FrozenFactorNormalization.SplitRatios
import Holant.Proofs.Reductions.FactorSaturation.Catalogue


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FactorSaturation
variable {L E : Type} [Field L] [Field E] (φ : L →+* E)

def slotLift {f : AnySignature E} (t : FactorTree f) (hf : f.2 ≠ 0) (U : KeyLift φ f) :
    (i : Slots t) → KeyLift φ (slot t i).1 :=
  match t with
  | .leaf _ _ => fun _ => U
  | .split S l r => fun i => match i with
      | .inl _ => U
      | .inr (.inl j) => slotLift l (S.factors_nonzero hf).1 (leftLift φ S hf U) j
      | .inr (.inr j) => slotLift r (S.factors_nonzero hf).2 (rightLift φ S hf U) j

variable {s : ℕ} (roots : Fin s → AnySignature E) (hn : ∀ i, (roots i).2 ≠ 0)
variable (rootLift : ∀ i, KeyLift φ (roots i))

def entryLift (j : Fin (addedCount roots hn)) : KeyLift φ (entry roots hn j) :=
  let u := enumerate roots hn j
  slotLift φ (tree roots hn u.1) (hn u.1) (rootLift u.1) (properSlot _ u.2)

def catalogueLift (i : Fin (s+addedCount roots hn)) : KeyLift φ (lookup roots hn i.val) := by
  by_cases hi : i.val < s
  · rw [show lookup roots hn i.val = roots ⟨i.val,hi⟩ from lookup_old roots hn ⟨i.val,hi⟩]
    exact rootLift ⟨i.val,hi⟩
  · let j : Fin (addedCount roots hn) := ⟨i.val-s,by omega⟩
    have he : i.val = s+j.val := by dsimp [j]; omega
    rw [he,lookup_new]
    exact entryLift φ roots hn rootLift j

theorem catalogue_exact (i : Fin (s+addedCount roots hn)) :
    RH.mapSignature φ (catalogueLift φ roots hn rootLift i).table =
      canonicalKey ((lookup roots hn i.val).2) :=
  (catalogueLift φ roots hn rootLift i).equation

/-- Transport only the signature index; the actual stored tree is unchanged. -/
def transportTree {a b : AnySignature E} (h : a = b) (t : FactorTree a) : FactorTree b :=
  h ▸ t
@[simp] theorem transportTree_leaves {a b : AnySignature E} (h : a = b) (t : FactorTree a) :
    (transportTree h t).leaves = t.leaves := by cases h; rfl

/-- The existing root tree or its stored subtree, never a new choice. -/
def catalogueTree (i : Fin (s+addedCount roots hn)) : FactorTree (lookup roots hn i.val) :=
  if hi : i.val < s then
    transportTree (lookup_old roots hn ⟨i.val,hi⟩).symm (tree roots hn ⟨i.val,hi⟩)
  else
    let j : Fin (addedCount roots hn) := ⟨i.val-s,by omega⟩
    have he : entry roots hn j = lookup roots hn i.val := by
      have hi' : i.val=s+j.val := by dsimp [j]; omega
      rw [hi',lookup_new]
    transportTree he (newNode roots hn (enumerate roots hn j)).2

theorem catalogueTree_leaves (i : Fin (s+addedCount roots hn)) :
    ∀ f ∈ (catalogueTree roots hn i).leaves,
      f ∈ Set.range (fun j : Fin (s+addedCount roots hn) => lookup roots hn j.val) := by
  intro f hf
  change f ∈ Set.range (fun j => (⟨arity roots hn j.val,augmented roots hn j⟩ : AnySignature E))
  rw [augmented_family]
  by_cases hi : i.val < s
  · have hh : f ∈ (tree roots hn ⟨i.val,hi⟩).leaves := by simpa [catalogueTree,hi] using hf
    exact leaves_retained roots hn ⟨i.val,hi⟩ f hh
  · let j : Fin (addedCount roots hn) := ⟨i.val-s,by omega⟩
    let u := enumerate roots hn j
    have hh : f ∈ (newNode roots hn u).2.leaves := by
      simpa [catalogueTree,hi,j,u] using hf
    exact leaves_retained roots hn u.1 f
      (stored_leaves_subset (slot_stored (tree roots hn u.1) (properSlot _ u.2)) f hh)

end Holant.LocalDrafts.Hardness.FrozenFactorNormalization
