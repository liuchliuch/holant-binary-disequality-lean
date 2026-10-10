import Holant.Proofs.FiniteGroups.Stabilization.QueueExhaustion
import Holant.Proofs.FiniteGroups.Stabilization.MinimumCore
import Mathlib.Data.List.OfFn


namespace Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
noncomputable section
variable {L κ : Type*} [Field L] [DecidableEq κ]

/-- Membership in the actual chosen tree, not existence of another
factorization of the same signature. -/
inductive StoredSubtree : TreeOccurrence L → TreeOccurrence L → Prop
  | root (t) : StoredSubtree t t
  | left {f a b} (s : ProperSplit f a b) (ta : FactorTree a) (tb : FactorTree b)
      {u} (h : StoredSubtree u ⟨a, ta⟩) : StoredSubtree u ⟨f, .split s ta tb⟩
  | right {f a b} (s : ProperSplit f a b) (ta : FactorTree a) (tb : FactorTree b)
      {u} (h : StoredSubtree u ⟨b, tb⟩) : StoredSubtree u ⟨f, .split s ta tb⟩

theorem StoredSubtree.arity_le {u t : TreeOccurrence L} (h : StoredSubtree u t) :
    u.1.1 ≤ t.1.1 := by
  induction h with
  | root => exact le_rfl
  | left s ta tb h ih => exact ih.trans s.left_lt.le
  | right s ta tb h ih => exact ih.trans s.right_lt.le

/-- Each chosen prime leaf appears with its original multiplicity and its
actual leaf tree. Equal signature values are not collapsed. -/
def leafOccurrences {f : AnySignature L} : FactorTree f → Multiset (TreeOccurrence L)
  | .leaf f hp => {⟨f, .leaf f hp⟩}
  | .split _ ta tb => leafOccurrences ta + leafOccurrences tb

theorem leafOccurrences_values {f : AnySignature L} (t : FactorTree f) :
    (leafOccurrences t).map Sigma.fst = t.leaves := by
  induction t with
  | leaf => rfl
  | split s ta tb iha ihb => simp [leafOccurrences, FactorTree.leaves, iha, ihb]

theorem leafOccurrences_stored {f : AnySignature L} (t : FactorTree f)
    (u : TreeOccurrence L) (hu : u ∈ leafOccurrences t) : StoredSubtree u ⟨f, t⟩ := by
  revert hu
  induction t with
  | leaf f hp =>
      intro hu
      have he := Multiset.mem_singleton.mp hu
      subst u
      exact .root _
  | split s ta tb iha ihb =>
      intro hu
      rcases Multiset.mem_add.mp hu with ha | hb
      · exact .left s ta tb (iha ha)
      · exact .right s ta tb (ihb hb)

theorem leafOccurrences_prime {f : AnySignature L} (t : FactorTree f)
    (u : TreeOccurrence L) (hu : u ∈ leafOccurrences t) : Prime u.1 := by
  apply t.leaves_prime
  rw [← leafOccurrences_values t]
  exact Multiset.mem_map.mpr ⟨u, hu, rfl⟩

theorem treeStep_preserves_stored {root : TreeOccurrence L}
    {W V : Multiset (TreeOccurrence L)} (h : TreeStep W V)
    (hV : ∀ t ∈ V, StoredSubtree t root) : ∀ t ∈ W, StoredSubtree t root := by
  have trans : ∀ {u v w : TreeOccurrence L}, StoredSubtree u v → StoredSubtree v w →
      StoredSubtree u w := by
    intro u v w huv hvw
    induction hvw with
    | root => exact huv
    | left s ta tb h ih => exact .left s ta tb (ih huv)
    | right s ta tb h ih => exact .right s ta tb (ih huv)
  cases h with
  | leaf f hp hn W => exact fun t ht => hV t (Multiset.mem_cons_of_mem ht)
  | split s ta tb W =>
      intro t ht
      have hparent := hV _ (Multiset.mem_cons_self _ _)
      rcases Multiset.mem_add.mp ht with ht | ht
      · rcases Multiset.mem_add.mp ht with ht | ht
        · have he : t = ⟨_, ta⟩ := by
            unfold openTree at ht
            split_ifs at ht with h
            · exact Multiset.mem_singleton.mp ht
            · simp at ht
          subst t
          exact trans (.left s ta tb (.root _)) hparent
        · have he : t = ⟨_, tb⟩ := by
            unfold openTree at ht
            split_ifs at ht with h
            · exact Multiset.mem_singleton.mp ht
            · simp at ht
          subst t
          exact trans (.right s ta tb (.root _)) hparent
      · exact hV t (Multiset.mem_cons_of_mem ht)

/-- A fixed finite physical output catalogue and already selected trees.
Actuality is relative to its recorded family, never inferred from a table
identity. Not every key need be a proper card; only spawning requires it. -/
structure Plan (L κ : Type*) [Field L] [DecidableEq κ] where
  core : TreeOccurrence L
  family : SignatureFamily L
  keys : Finset κ
  card : κ → TreeOccurrence L
  actual : ∀ k ∈ keys, Gadget.Realizes family .disequality (card k).1.2

variable {n : ℕ} (roots : Fin n → TreeOccurrence L)

/-- The child remembers the original index, exact selected parent card,
exact stored subtree and the parent queue in which its key was consumed.
The constructor is not a claim of Turing access to that subtree. -/
inductive Origin : TreeOccurrence L → Type _
  | original (i : Fin n) : Origin (roots i)
  | child (P : Plan L κ) (parent : Origin P.core)
      (q : FrozenQueue L P.keys)
      (run : FrozenQueue.Runs (FrozenQueue.initial P.keys P.card) q)
      (k : κ) (pending : k ∈ q.todo) (exhausted : q.work k = 0)
      (ordinal : ℕ) (t : TreeOccurrence L) (stored : StoredSubtree t (P.card k))
      (proper : (P.card k).1.1 < P.core.1.1) : Origin t

variable {roots}

def Origin.originalIndex {t : TreeOccurrence L} : Origin (κ := κ) roots t → Fin n
  | .original i => i
  | .child _ p _ _ _ _ _ _ _ _ _ => p.originalIndex

def Origin.path {t : TreeOccurrence L} : Origin (κ := κ) roots t → List (κ × ℕ)
  | .original _ => []
  | .child _ p _ _ k _ _ j _ _ _ => p.path ++ [(k, j)]

/-- Ancestor keys are completed provenance, separate from the child's
new local FrozenQueue. A receipt identifies the parent's path and key. -/
def Origin.receipts {t : TreeOccurrence L} : Origin (κ := κ) roots t →
    List (List (κ × ℕ) × κ)
  | .original _ => []
  | .child _ p _ _ k _ _ _ _ _ _ => p.receipts ++ [(p.path, k)]

/-- Each frame keeps a real finite run of the old frozen queue. A caller
cannot replace it by an unrelated equal-arity catalogue in a local step. -/
structure Frame (roots : Fin n → TreeOccurrence L) where
  plan : Plan L κ
  origin : Origin (κ := κ) roots plan.core
  queue : FrozenQueue L plan.keys
  run : FrozenQueue.Runs (FrozenQueue.initial plan.keys plan.card) queue

def Frame.advance (p : Frame (κ := κ) roots) (q : FrozenQueue L p.plan.keys)
    (h : FrozenQueue.Step q p.queue) : Frame (κ := κ) roots :=
  ⟨p.plan, p.origin, q, p.run.trans (Relation.ReflTransGen.single h)⟩

def Frame.child (p : Frame (κ := κ) roots) (k : κ) (hk : k ∈ p.queue.todo)
    (he : p.queue.work k = 0) (j : ℕ) (C : Plan L κ)
    (hs : StoredSubtree C.core (p.plan.card k))
    (hp : (p.plan.card k).1.1 < p.plan.core.1.1) : Frame (κ := κ) roots :=
  ⟨C, .child p.plan p.origin p.queue p.run k hk he j C.core hs hp,
    FrozenQueue.initial C.keys C.card, .refl⟩

theorem Frame.child_arity_lt (p : Frame (κ := κ) roots) (k : κ) (hk : k ∈ p.queue.todo)
    (he : p.queue.work k = 0) (j : ℕ) (C : Plan L κ)
    (hs : StoredSubtree C.core (p.plan.card k))
    (hp : (p.plan.card k).1.1 < p.plan.core.1.1) :
    (p.child k hk he j C hs hp).plan.core.1.1 < p.plan.core.1.1 :=
  hs.arity_le.trans_lt hp

/-- The inherited originating key is recorded as completed in the
predecessor queue. Child-local keys are scoped by a new appended slot. -/
theorem consumed_parent_key (p : Frame (κ := κ) roots) (k : κ) (hk : k ∈ p.queue.todo) :
    k ∈ (p.queue.finish k).done ∧ k ∉ (p.queue.finish k).todo := by
  constructor
  · exact Finset.mem_sdiff.mpr ⟨p.queue.within hk, by simp [FrozenQueue.finish]⟩
  · simp [FrozenQueue.finish]

theorem Frame.selected_card_actual (p : Frame (κ := κ) roots) (k : κ)
    (hk : k ∈ p.queue.todo) :
    Gadget.Realizes p.plan.family .disequality (p.plan.card k).1.2 :=
  p.plan.actual k (p.queue.within hk)

theorem Frame.child_receipt (p : Frame (κ := κ) roots) (k : κ) (hk : k ∈ p.queue.todo)
    (he : p.queue.work k = 0) (j : ℕ) (C : Plan L κ)
    (hs : StoredSubtree C.core (p.plan.card k))
    (hp : (p.plan.card k).1.1 < p.plan.core.1.1) :
    (p.origin.path, k) ∈ (p.child k hk he j C hs hp).origin.receipts ∧
      k ∈ (p.queue.finish k).done := by
  exact ⟨by simp [Frame.child, Origin.receipts], (consumed_parent_key p k hk).1⟩

structure Slot (roots : Fin n → TreeOccurrence L) where
  frame : Frame (κ := κ) roots
  active : Bool

def Slot.pending (s : Slot (κ := κ) roots) : Finset κ := if s.active then s.frame.queue.todo else ∅
def Slot.processed (s : Slot (κ := κ) roots) : Finset κ := s.frame.plan.keys \ s.pending

theorem Slot.pending_within (s : Slot (κ := κ) roots) : s.pending ⊆ s.frame.plan.keys := by
  cases h : s.active with
  | false => simp [Slot.pending, h]
  | true => simpa [Slot.pending, h] using s.frame.queue.within

theorem Slot.partition (s : Slot (κ := κ) roots) : s.processed ∪ s.pending = s.frame.plan.keys :=
  Finset.sdiff_union_of_subset s.pending_within

theorem Slot.disjoint (s : Slot (κ := κ) roots) : Disjoint s.processed s.pending := by
  apply Finset.disjoint_left.mpr
  intro k hk hp
  exact (Finset.mem_sdiff.mp hk).2 hp

def initial (P : Fin n → Plan L κ) (hP : ∀ i, (P i).core = roots i) : List (Slot (κ := κ) roots) :=
  List.ofFn (fun i => ⟨⟨P i, (hP i).symm ▸ Origin.original i,
    FrozenQueue.initial (P i).keys (P i).card, .refl⟩, true⟩)

theorem initial_length (P : Fin n → Plan L κ) (hP : ∀ i, (P i).core = roots i) :
    (initial P hP).length = n := by simp [initial]

end
end Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
