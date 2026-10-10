import Holant.Proofs.FiniteGroups.Stabilization.ExactGroupBound
import Holant.Proofs.FiniteGroups.Stabilization.Termination


namespace Holant.LocalDrafts.FinitePGL2.Stabilization.Node
noncomputable section
variable {L κ : Type*} [Field L] [NumberField L] [DecidableEq κ]

def sourceOmega (s : Node L κ) : Rank :=
  (sourceGroupDefect s.family s.torsion,
    (s.core.signature.1, (s.queue.todo.card, s.queue.potential)))

theorem source_step_decreases {t s : Node L κ} (h : Step t s) :
    RankLT t.sourceOmega s.sourceOmega := by
  cases h with
  | group s t hr hs =>
      exact Prod.Lex.left _ _ (sourceGroupDefect_lt_of_strict s.torsion t.torsion hs)
  | arity s t hr he ha =>
      have hd : sourceGroupDefect t.family t.torsion = sourceGroupDefect s.family s.torsion := by
        unfold sourceGroupDefect
        rw [he]
      change RankLT (sourceGroupDefect t.family t.torsion, _) (sourceGroupDefect s.family s.torsion, _)
      rw [hd]
      exact Prod.Lex.right _ (Prod.Lex.left _ _ ha)
  | «local» s q hq =>
      exact Prod.Lex.right _ (Prod.Lex.right _ (FrozenQueue.step_decreases hq))
  | retainedLocal s t hr he ha hk hq =>
      have hd : sourceGroupDefect t.family t.torsion = sourceGroupDefect s.family s.torsion := by
        unfold sourceGroupDefect
        rw [he]
      have hl := FrozenQueue.step_decreases hq
      have transport_measure : ∀ {U V : Finset κ} (h : U = V) (q : FrozenQueue L U),
          (h ▸ q).measure = q.measure := by intro U V h q; cases h; rfl
      have hm : (hk ▸ t.queue).measure = t.queue.measure := transport_measure hk t.queue
      rw [hm] at hl
      change RankLT (sourceGroupDefect t.family t.torsion, (t.core.signature.1, t.queue.measure))
        (sourceGroupDefect s.family s.torsion, (s.core.signature.1, s.queue.measure))
      rw [hd, ha]
      exact Prod.Lex.right _ (Prod.Lex.right _ hl)

theorem source_step_wellFounded : WellFounded (Step (L := L) (κ := κ)) :=
  Subrelation.wf (fun h => source_step_decreases h) (InvImage.wf sourceOmega rank_wellFounded)

end
end Holant.LocalDrafts.FinitePGL2.Stabilization.Node
