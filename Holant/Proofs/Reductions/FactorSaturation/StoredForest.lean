import Holant.Proofs.FiniteGroups.Stabilization.OccurrenceSchedule.Stored
import Holant.Proofs.FiniteGroups.Stabilization.LeafExposure
import Holant.Proofs.FiniteGroups.Stabilization.RetainedBatch


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FactorSaturation
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
variable {K : Type} [Field K]

def Slots {f : AnySignature K} : FactorTree f → Type
  | .leaf _ _ => Unit
  | .split _ l r => Unit ⊕ (Slots l ⊕ Slots r)

instance slotsFintype {f : AnySignature K} (t : FactorTree f) : Fintype (Slots t) := by
  induction t with
  | leaf => exact inferInstanceAs (Fintype Unit)
  | split s l r il ir =>
      letI := il
      letI := ir
      exact inferInstanceAs (Fintype (Unit ⊕ (Slots l ⊕ Slots r)))

def slot {f : AnySignature K} (t : FactorTree f) : Slots t → TreeOccurrence K :=
  match t with
  | .leaf f p => fun _ => ⟨f, .leaf f p⟩
  | .split s l r => Sum.elim (fun _ => ⟨_, .split s l r⟩)
      (Sum.elim (slot l) (slot r))

def path {f : AnySignature K} (t : FactorTree f) : Slots t → List Bool :=
  match t with
  | .leaf _ _ => fun _ => []
  | .split _ l r => Sum.elim (fun _ => [])
      (Sum.elim (fun i => false :: path l i) (fun i => true :: path r i))

theorem slot_stored {f : AnySignature K} (t : FactorTree f) (i : Slots t) :
    StoredSubtree (slot t i) ⟨f,t⟩ := by
  induction t with
  | leaf => exact .root _
  | split s l r il ir =>
      rcases i with u | (i | i)
      · exact .root _
      · exact .left s l r (il i)
      · exact .right s l r (ir i)

theorem path_injective {f : AnySignature K} (t : FactorTree f) : Function.Injective (path t) := by
  induction t with
  | leaf => intro a b _; exact @Subsingleton.elim Unit _ a b
  | split s l r il ir =>
      intro a b he
      rcases a with a | (a | a) <;> rcases b with b | (b | b)
      all_goals simp only [path, Sum.elim_inl, Sum.elim_inr, List.cons.injEq] at he
      all_goals first
        | exact congrArg Sum.inl (Subsingleton.elim _ _)
        | exact congrArg (fun x => Sum.inr (Sum.inl x)) (il he.2)
        | exact congrArg (fun x => Sum.inr (Sum.inr x)) (ir he.2)
        | simp_all

def ProperSlots {f : AnySignature K} : FactorTree f → Type
  | .leaf _ _ => Empty
  | .split _ l r => Slots l ⊕ Slots r
instance properSlotsFintype {f : AnySignature K} (t : FactorTree f) : Fintype (ProperSlots t) := by
  cases t with
  | leaf => exact inferInstanceAs (Fintype Empty)
  | split s l r => exact inferInstanceAs (Fintype (Slots l ⊕ Slots r))

def properSlot {f : AnySignature K} (t : FactorTree f) : ProperSlots t → Slots t :=
  match t with
  | .leaf _ _ => Empty.elim
  | .split _ _ _ => Sum.inr

theorem proper_arity_lt {f : AnySignature K} (t : FactorTree f) (i : ProperSlots t) :
    (slot t (properSlot t i)).1.1 < f.1 := by
  cases t with
  | leaf => exact Empty.elim i
  | split s l r =>
      cases i with
      | inl i => exact (slot_stored l i).arity_le.trans_lt s.left_lt
      | inr i => exact (slot_stored r i).arity_le.trans_lt s.right_lt

theorem stored_nonzero {u t : TreeOccurrence K} (h : StoredSubtree u t)
    (hn : t.1.2 ≠ 0) : u.1.2 ≠ 0 := by
  revert hn
  induction h with
  | root => exact fun hn => hn
  | left s l r h ih => exact fun hn => ih (s.factors_nonzero hn).1
  | right s l r h ih => exact fun hn => ih (s.factors_nonzero hn).2

theorem stored_positive {u t : TreeOccurrence K} (h : StoredSubtree u t)
    (hp : 0 < t.1.1) : 0 < u.1.1 := by
  revert hp
  induction h with
  | root => exact fun hp => hp
  | left s l r h ih => exact fun _ => ih s.left_pos
  | right s l r h ih => exact fun _ => ih s.right_pos

/-- Composed provenance for ANY stored intermediate, not just a prime leaf. -/
theorem stored_root_or_split {u t : TreeOccurrence K} (h : StoredSubtree u t) :
    t.1 = u.1 ∨ ∃ b, Nonempty (ProperSplit t.1 u.1 b) := by
  induction h with
  | root => exact Or.inl rfl
  | @left f a b s l r u h ih =>
      rcases ih with he | ⟨b, ⟨q⟩⟩
      · apply Or.inr
        refine ⟨b, ?_⟩
        rw [← he]
        exact ⟨s⟩
      · exact Or.inr ⟨_, ⟨s.composeLeft q⟩⟩
  | @right f a b s l r u h ih =>
      rcases ih with he | ⟨b, ⟨q⟩⟩
      · apply Or.inr
        refine ⟨a, ?_⟩
        rw [← he]
        exact ⟨s.swap⟩
      · exact Or.inr ⟨_, ⟨s.swap.composeLeft q⟩⟩

theorem proper_split {f : AnySignature K} (t : FactorTree f) (i : ProperSlots t) :
    ∃ b, Nonempty (ProperSplit f (slot t (properSlot t i)).1 b) := by
  rcases stored_root_or_split (slot_stored t (properSlot t i)) with he | hs
  · have hl := proper_arity_lt t i
    have ha := congrArg Sigma.fst he
    change f.1 = (slot t (properSlot t i)).1.1 at ha
    omega
  · exact hs

variable {s : ℕ} (roots : Fin s → AnySignature K) (hn : ∀ i, (roots i).2 ≠ 0)

/-- Trees are constructed here; forest completeness is not an input premise. -/
def tree (i : Fin s) : FactorTree (roots i) := Classical.choice (exists_factorTree (roots i) (hn i))
abbrev Node := Σ i : Fin s, Slots (tree roots hn i)
abbrev NewNode := Σ i : Fin s, ProperSlots (tree roots hn i)
def node (i : Node roots hn) : TreeOccurrence K := slot (tree roots hn i.1) i.2
def newNode (i : NewNode roots hn) : TreeOccurrence K :=
  slot (tree roots hn i.1) (properSlot (tree roots hn i.1) i.2)
def newPath (i : NewNode roots hn) : Fin s × List Bool :=
  (i.1, path (tree roots hn i.1) (properSlot (tree roots hn i.1) i.2))

theorem new_nonzero (i : NewNode roots hn) : (newNode roots hn i).1.2 ≠ 0 :=
  stored_nonzero (slot_stored _ _) (hn i.1)
theorem new_positive (hp : ∀ i, 0 < (roots i).1) (i : NewNode roots hn) :
    0 < (newNode roots hn i).1.1 := stored_positive (slot_stored _ _) (hp i.1)

/-- Every emitted node keeps its own chosen subtree; each of its leaves is
prime, even when the emitted node itself is a retained composite. -/
theorem node_leaves_prime (i : Node roots hn) (a : AnySignature K)
    (ha : a ∈ (node roots hn i).2.leaves) : Prime a := (node roots hn i).2.leaves_prime a ha

end Holant.LocalDrafts.Hardness.FactorSaturation
