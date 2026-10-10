import Holant.Proofs.FiniteGroups.Stabilization.ActualGroups
import Holant.Proofs.FiniteGroups.Stabilization.FrozenWorklist
import Holant.Proofs.FiniteGroups.Stabilization.MinimumCore


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

open Holant.Projective.BoundedTorsion
noncomputable section
variable {L κ : Type*} [Field L] [NumberField L] [DecidableEq κ]

structure Node (L κ : Type*) [Field L] [NumberField L] [DecidableEq κ] where
  family : SignatureFamily L
  finite : family.Finite
  equality : (⟨2, binarySignature Signature.equality⟩ : AnySignature L) ∈ family
  torsion : ResidualTorsion family
  core : MinimumCore family
  frozen : Finset κ
  queue : FrozenQueue L frozen

namespace Node

def withQueue (s : Node L κ) (q : FrozenQueue L s.frozen) : Node L κ := { s with queue := q }

abbrev Rank := ℕ × (ℕ × (ℕ × ℕ))
abbrev RankLT : Rank → Rank → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)))

def omega (s : Node L κ) : Rank :=
  (groupDefect s.family s.torsion,
    (s.core.signature.1, (s.queue.todo.card, s.queue.potential)))

theorem rank_wellFounded : WellFounded RankLT :=
  Nat.lt_wfRel.wf.prod_lex (Nat.lt_wfRel.wf.prod_lex (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf))

/-- Source 5.11's continuing transitions as concrete changes.  No constructor
takes an Omega inequality.  A retained local step must preserve the complete
group, minimum arity, and frozen key set and must process a stored tree;
changing family alone is not a valid local successor. -/
inductive Step : Node L κ → Node L κ → Prop
  | group (s t : Node L κ) (retained : s.family ⊆ t.family)
      (strict : completeGroup s.family s.torsion < completeGroup t.family t.torsion) : Step t s
  | arity (s t : Node L κ) (retained : s.family ⊆ t.family)
      (sameGroup : completeGroup t.family t.torsion = completeGroup s.family s.torsion)
      (smaller : t.core.signature.1 < s.core.signature.1) : Step t s
  | local (s : Node L κ) (q : FrozenQueue L s.frozen) (step : FrozenQueue.Step q s.queue) :
      Step (s.withQueue q) s
  | retainedLocal (s t : Node L κ) (retained : s.family ⊆ t.family)
      (sameGroup : completeGroup t.family t.torsion = completeGroup s.family s.torsion)
      (sameArity : t.core.signature.1 = s.core.signature.1)
      (sameKeys : t.frozen = s.frozen)
      (step : FrozenQueue.Step (sameKeys ▸ t.queue) s.queue) : Step t s

theorem step_decreases {t s : Node L κ} (h : Step t s) : RankLT t.omega s.omega := by
  cases h with
  | group s t hret hstrict =>
      exact Prod.Lex.left _ _ (groupDefect_lt_of_strict s.torsion t.torsion hstrict)
  | arity s t hret he hlt =>
      have hd : groupDefect t.family t.torsion = groupDefect s.family s.torsion := by
        unfold groupDefect
        rw [he]
      change RankLT (groupDefect t.family t.torsion, _) (groupDefect s.family s.torsion, _)
      rw [hd]
      exact Prod.Lex.right _ (Prod.Lex.left _ _ hlt)
  | «local» s q hq =>
      exact Prod.Lex.right _ (Prod.Lex.right _ (FrozenQueue.step_decreases hq))
  | retainedLocal s t hret he ha hk hq =>
      have hd : groupDefect t.family t.torsion = groupDefect s.family s.torsion := by
        unfold groupDefect
        rw [he]
      have hl := FrozenQueue.step_decreases hq
      have transport_measure : ∀ {U V : Finset κ} (h : U = V) (q : FrozenQueue L U),
          (h ▸ q).measure = q.measure := by
        intro U V h q
        cases h
        rfl
      have hm : (hk ▸ t.queue).measure = t.queue.measure := transport_measure hk t.queue
      rw [hm] at hl
      change RankLT (groupDefect t.family t.torsion, (t.core.signature.1, t.queue.measure))
        (groupDefect s.family s.torsion, (s.core.signature.1, s.queue.measure))
      rw [hd, ha]
      exact Prod.Lex.right _ (Prod.Lex.right _ hl)

theorem step_wellFounded : WellFounded (Step (L := L) (κ := κ)) :=
  Subrelation.wf (fun h => step_decreases h) (InvImage.wf omega rank_wellFounded)

theorem no_infinite_continuation (s : ℕ → Node L κ) : ¬ ∀ n, Step (s (n + 1)) (s n) := by
  intro h
  exact (wellFounded_iff_isEmpty_descending_chain.mp step_wellFounded).false ⟨s, h⟩

/-- The strict arity edge can be obtained from an actual frozen factor tree;
the caller need not supply the measure decrease as a separate premise. -/
theorem step_of_card_leaf (s t : Node L κ) (hret : s.family ⊆ t.family)
    (hG : completeGroup t.family t.torsion = completeGroup s.family s.torsion)
    (card : AnySignature L) (hcard : card.1 + 2 = s.core.signature.1)
    (tree : FactorTree card) (leaf : AnySignature L) (hleaf : leaf ∈ tree.leaves)
    (hleafret : leaf ∈ t.family) (hnb : 3 ≤ leaf.1) : Step t s :=
  .arity s t hret hG (smaller_core_of_card_leaf s.core t.core card hcard tree leaf hleaf hleafret hnb)

end Node
end
end Holant.LocalDrafts.FinitePGL2.Stabilization
