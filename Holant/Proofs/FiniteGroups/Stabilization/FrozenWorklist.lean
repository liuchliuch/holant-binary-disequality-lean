import Mathlib.Logic.Function.Basic
import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist
import Mathlib.Data.Finset.Card
import Mathlib.Order.RelClasses


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

open scoped BigOperators
noncomputable section
variable {L : Type*} [Field L]

abbrev TreeOccurrence (L : Type*) [Field L] := Σ f : AnySignature L, FactorTree f

def treePotential (W : Multiset (TreeOccurrence L)) : ℕ :=
  (W.map (fun t => t.1.1 - 1)).sum

@[simp] theorem treePotential_zero : treePotential (0 : Multiset (TreeOccurrence L)) = 0 := rfl

@[simp] theorem treePotential_add (W V : Multiset (TreeOccurrence L)) :
    treePotential (W + V) = treePotential W + treePotential V := by simp [treePotential]

@[simp] theorem treePotential_cons (t : TreeOccurrence L) (W : Multiset (TreeOccurrence L)) :
    treePotential (t ::ₘ W) = (t.1.1 - 1) + treePotential W := by simp [treePotential]

def openTree (t : TreeOccurrence L) : Multiset (TreeOccurrence L) :=
  if 2 ≤ t.1.1 then {t} else 0

@[simp] theorem treePotential_openTree (t : TreeOccurrence L) :
    treePotential (openTree t) = t.1.1 - 1 := by
  by_cases h : 2 ≤ t.1.1
  · simp [openTree, h, treePotential]
  · have hz : t.1.1 - 1 = 0 := by omega
    simp [openTree, h, hz]

/-- Only the precise stored leaf or stored split may be processed. -/
inductive TreeStep : Multiset (TreeOccurrence L) → Multiset (TreeOccurrence L) → Prop
  | leaf (f : AnySignature L) (hp : Prime f) (hn : 2 ≤ f.1) (W) :
      TreeStep W (⟨f, .leaf f hp⟩ ::ₘ W)
  | split {f a b : AnySignature L} (s : ProperSplit f a b)
      (ta : FactorTree a) (tb : FactorTree b) (W) :
      TreeStep (openTree ⟨a, ta⟩ + openTree ⟨b, tb⟩ + W)
        (⟨f, .split s ta tb⟩ ::ₘ W)

theorem treeStep_decreases {W V : Multiset (TreeOccurrence L)} (h : TreeStep W V) :
    treePotential W < treePotential V := by
  cases h with
  | leaf f hp hn W => simp only [treePotential_cons]; omega
  | split s ta tb W =>
      simp only [treePotential_add, treePotential_openTree, treePotential_cons]
      have := s.arity
      have := s.left_pos
      have := s.right_pos
      omega

theorem treeStep_wellFounded : WellFounded (TreeStep (L := L)) :=
  Subrelation.wf (fun h => treeStep_decreases h) (measure treePotential).wf

variable {κ : Type*} [DecidableEq κ]

/-- The finite key set U is a parameter, hence remains frozen across all local
steps. Occurrences inside an attached tree retain their multiplicity. -/
structure FrozenQueue (L : Type*) [Field L] (U : Finset κ) where
  todo : Finset κ
  within : todo ⊆ U
  work : κ → Multiset (TreeOccurrence L)

namespace FrozenQueue

variable {U : Finset κ}

def done (q : FrozenQueue L U) : Finset κ := U \ q.todo
def potential (q : FrozenQueue L U) : ℕ := ∑ k ∈ q.todo, treePotential (q.work k)

theorem partition (q : FrozenQueue L U) : q.done ∪ q.todo = U := by
  exact Finset.sdiff_union_of_subset q.within

theorem done_disjoint (q : FrozenQueue L U) : Disjoint q.done q.todo := by
  apply Finset.disjoint_left.mpr
  intro k hk ht
  exact (Finset.mem_sdiff.mp hk).2 ht

def initial (U : Finset κ) (root : κ → TreeOccurrence L) : FrozenQueue L U :=
  ⟨U, fun _ h => h, fun k => openTree (root k)⟩

/-- Removal is only exposed as a continuing step below when the tree is exhausted. -/
def finish (q : FrozenQueue L U) (k : κ) : FrozenQueue L U :=
  ⟨q.todo.erase k, (Finset.erase_subset _ _).trans q.within, q.work⟩

def process (q : FrozenQueue L U) (k : κ) (W : Multiset (TreeOccurrence L)) :
    FrozenQueue L U := ⟨q.todo, q.within, Function.update q.work k W⟩

theorem finish_card_lt (q : FrozenQueue L U) {k : κ} (hk : k ∈ q.todo) :
    (q.finish k).todo.card < q.todo.card := by
  exact Finset.card_erase_lt_of_mem hk

theorem process_potential_lt (q : FrozenQueue L U) {k : κ} (hk : k ∈ q.todo)
    {W : Multiset (TreeOccurrence L)} (h : TreeStep W (q.work k)) :
    (q.process k W).potential < q.potential := by
  change (∑ j ∈ q.todo, treePotential (Function.update q.work k W j)) <
    ∑ j ∈ q.todo, treePotential (q.work j)
  apply Finset.sum_lt_sum
  · intro j hj
    by_cases he : j = k
    · subst j
      simpa only [Function.update_self] using (treeStep_decreases h).le
    · simp only [Function.update_of_ne he]
      exact le_rfl
  · exact ⟨k, hk, by simpa only [Function.update_self] using treeStep_decreases h⟩

/-- Equal-stratum processing cannot introduce a key not already in todo. -/
inductive Step : FrozenQueue L U → FrozenQueue L U → Prop
  | finish (q : FrozenQueue L U) (k : κ) (hk : k ∈ q.todo) (hexhausted : q.work k = 0) :
      Step (q.finish k) q
  | process (q : FrozenQueue L U) (k : κ) (hk : k ∈ q.todo)
      (W : Multiset (TreeOccurrence L)) (h : TreeStep W (q.work k)) :
      Step (q.process k W) q

theorem step_todo_subset {q' q : FrozenQueue L U} (h : Step q' q) : q'.todo ⊆ q.todo := by
  cases h with
  | finish q k hk he => exact Finset.erase_subset _ _
  | process q k hk W he => exact fun _ h => h

theorem step_done_subset {q' q : FrozenQueue L U} (h : Step q' q) : q.done ⊆ q'.done := by
  intro k hk
  simp only [done, Finset.mem_sdiff] at hk ⊢
  exact ⟨hk.1, fun hn => hk.2 (step_todo_subset h hn)⟩

def measure (q : FrozenQueue L U) : ℕ × ℕ := (q.todo.card, q.potential)

theorem step_decreases {q' q : FrozenQueue L U} (h : Step q' q) :
    Prod.Lex (· < ·) (· < ·) q'.measure q.measure := by
  cases h with
  | finish q k hk he => exact Prod.Lex.left _ _ (finish_card_lt q hk)
  | process q k hk W he => exact Prod.Lex.right _ (process_potential_lt q hk he)

theorem step_wellFounded : WellFounded (Step (L := L) (U := U)) :=
  Subrelation.wf (fun h => step_decreases h)
    (InvImage.wf measure (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf))

end FrozenQueue
end
end Holant.LocalDrafts.FinitePGL2.Stabilization
