import Holant.Proofs.FiniteGroups.Stabilization.OccurrenceSchedule.Stored
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn

/-! Original saved prime occurrences, with physical multiplicity retained.
An address is a branch address in the actual saved tree. It is not a quotient
by signature equality, projective equivalence, or current minimum arity.
This catalogue does not assert a rigidity or complexity theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.Occurrences
open Holant
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule

variable {L : Type*} [Field L]

/-- The left and right branches are distinct even if their signatures agree. -/
def Address {f : AnySignature L} : FactorTree f → Type
  | .leaf _ _ => Unit
  | .split _ left right => Address left ⊕ Address right

instance addressFintype {f : AnySignature L} (t : FactorTree f) : Fintype (Address t) :=
  match t with
  | .leaf _ _ => inferInstanceAs (Fintype Unit)
  | .split _ left right => by
      letI := addressFintype left
      letI := addressFintype right
      exact inferInstanceAs (Fintype (Address left ⊕ Address right))

/-- The exact selected leaf tree, including the saved prime proof. -/
def leaf {f : AnySignature L} (t : FactorTree f) : Address t → TreeOccurrence L :=
  match t with
  | .leaf f hp => fun _ => ⟨f, .leaf f hp⟩
  | .split _ left right => Sum.elim (leaf left) (leaf right)

/-- Ordered branch addresses do not select an independent factorization. -/
theorem leaf_stored {f : AnySignature L} (t : FactorTree f) (p : Address t) :
    StoredSubtree (leaf t p) ⟨f, t⟩ := by
  induction t with
  | leaf f hp => exact .root _
  | split s left right ihl ihr =>
      cases p with
      | inl p => exact .left s left right (ihl p)
      | inr p => exact .right s left right (ihr p)

theorem leaf_mem {f : AnySignature L} (t : FactorTree f) (p : Address t) :
    (leaf t p).1 ∈ t.leaves := by
  induction t with
  | leaf f hp => simp [leaf, FactorTree.leaves]
  | split s left right ihl ihr =>
      cases p with
      | inl p => exact Multiset.mem_add.mpr (.inl (ihl p))
      | inr p => exact Multiset.mem_add.mpr (.inr (ihr p))

/-- Every stored prime leaf value is represented by a saved branch address. -/
theorem leaf_address_complete {f : AnySignature L} (t : FactorTree f)
    (a : AnySignature L) (ha : a ∈ t.leaves) : ∃ p : Address t, (leaf t p).1 = a := by
  induction t with
  | leaf f hp =>
      have he : a = f := by simpa [FactorTree.leaves] using ha
      exact ⟨(), he.symm⟩
  | split s left right ihl ihr =>
      rcases Multiset.mem_add.mp ha with hl | hr
      · obtain ⟨p, hp⟩ := ihl hl
        exact ⟨.inl p, hp⟩
      · obtain ⟨p, hp⟩ := ihr hr
        exact ⟨.inr p, hp⟩

theorem leaf_prime {f : AnySignature L} (t : FactorTree f) (p : Address t) :
    Prime (leaf t p).1 := t.leaves_prime _ (leaf_mem t p)

theorem leaf_positive {f : AnySignature L} (t : FactorTree f) (hp : 0 < f.1)
    (p : Address t) : 0 < (leaf t p).1.1 := by
  revert hp p
  induction t with
  | leaf f prime =>
      intro hp p
      exact hp
  | split s left right ihl ihr =>
      intro hp p
      cases p with
      | inl p => exact ihl s.left_pos p
      | inr p => exact ihr s.right_pos p

/-- Exact dependent branch-address transport across whole saved-tree equality. -/
def transportAddress {u v : TreeOccurrence L} (h : u = v) : Address u.2 → Address v.2 := by
  cases h
  exact id

theorem transportAddress_injective {u v : TreeOccurrence L} (h : u = v) :
    Function.Injective (transportAddress h) := by
  cases h
  exact Function.injective_id

theorem transportAddress_leaf {u v : TreeOccurrence L} (h : u = v) (p : Address u.2) :
    leaf v.2 (transportAddress h p) = leaf u.2 p := by
  cases h
  rfl

/-- Transport is across equality of the entire saved occurrence, not merely
its signature value or the existence of another factorization. -/
theorem leaf_transport {u v : TreeOccurrence L} (h : u = v) (p : Address u.2) :
    ∃ q : Address v.2, leaf v.2 q = leaf u.2 p := by
  cases h
  exact ⟨p, rfl⟩

/-- The number of addresses is the multiset leaf count, not its support size. -/
theorem address_card {f : AnySignature L} (t : FactorTree f) :
    Fintype.card (Address t) = t.leaves.card := by
  induction t with
  | leaf f hp =>
      have he : Fintype.card (Address (.leaf f hp)) = Fintype.card Unit :=
        Fintype.card_congr (show Address (.leaf f hp) ≃ Unit from Equiv.refl Unit)
      exact he.trans Fintype.card_unit
  | split s left right ihl ihr =>
      have he : Fintype.card (Address (.split s left right)) =
          Fintype.card (Address left ⊕ Address right) :=
        Fintype.card_congr
          (show Address (.split s left right) ≃ Address left ⊕ Address right from Equiv.refl _)
      calc
        Fintype.card (Address (.split s left right)) =
            Fintype.card (Address left ⊕ Address right) := he
        _ = Fintype.card (Address left) + Fintype.card (Address right) := Fintype.card_sum
        _ = left.leaves.card + right.leaves.card := congrArg₂ (· + ·) ihl ihr
        _ = (FactorTree.split s left right).leaves.card := by
          simp only [FactorTree.leaves, Multiset.card_add]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.Occurrences
end
