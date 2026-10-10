import Holant.Proofs.FiniteGroups.Stabilization.Dispatch
import Holant.Proofs.FiniteGroups.Stabilization.FrozenDeck
import Holant.Proofs.FiniteGroups.Stabilization.RawRealization


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
attribute [local instance] Classical.propDecidable
variable {L κ : Type*} [Field L] [NumberField L] [DecidableEq κ]

namespace Node

/-- A real nonbinary card leaf forces an outer successor even when the
exposure also changes the complete group.  The caller supplies neither the
group-change case nor the strict arity inequality. -/
theorem step_of_frozen_leaf {m : ℕ} (s t : Node L κ)
    (f : Signature L (m + 2)) (hcore : s.core.signature = ⟨m + 2, f⟩)
    (hret : retainFrozenDeck s.family s.torsion f ⊆ t.family)
    (token : CanonicalToken s.family s.torsion f) (a : AnySignature L)
    (ha : a ∈ (selectedCardTree s.family s.torsion f token).2.leaves) (hnb : 3 ≤ a.1) :
    Step t s := by
  have hFG : s.family ⊆ t.family := (retainBatch_retains s.family _ _).trans hret
  rcases completeGroup_eq_or_lt hFG s.torsion t.torsion with he | hs
  · apply Step.arity s t hFG he.symm
    have hn : s.core.signature.1 = m + 2 := congrArg Sigma.fst hcore
    exact smaller_core_of_card_leaf s.core t.core
      (selectedCardTree s.family s.torsion f token).1 hn.symm
      (selectedCardTree s.family s.torsion f token).2 a ha
      (hret (frozen_leaf_retained s.family s.torsion f token a ha)) hnb
  · exact Step.group s t hFG hs

/-- Exposing the concrete frozen batch either gives an actual infinite-order
binary witness or permits reconstruction of a minimum core and a complete
finite group.  This does not identify the witness with a hardness theorem. -/
theorem frozen_batch_residual_dispatch {m : ℕ} (s : Node L κ) (f : Signature L (m + 2)) :
    let G := retainFrozenDeck s.family s.torsion f
    (∃ B, ActualNonsingular G B ∧ ¬ ProjectivelyFinite (transfer B)) ∨
      ∃ hG : ResidualTorsion G, ∃ core : MinimumCore G,
        core.signature.1 ≤ s.core.signature.1 ∧
        (completeGroup s.family s.torsion = completeGroup G hG ∨
          completeGroup s.family s.torsion < completeGroup G hG) := by
  dsimp only
  let G := retainFrozenDeck s.family s.torsion f
  have hFG : s.family ⊆ G := retainBatch_retains s.family _ _
  rcases residual_or_actual_infinite G with hG | hbad
  · obtain ⟨core⟩ := exists_minimumCore G
      ⟨s.core.signature, hFG s.core.retained, s.core.prime, s.core.nonbinary⟩
    exact Or.inr ⟨hG, core, MinimumCore.arity_nonincrease hFG s.core core,
      completeGroup_eq_or_lt hFG s.torsion hG⟩
  · exact Or.inl hbad

end Node
end
end Holant.LocalDrafts.FinitePGL2.Stabilization
