import Holant.Proofs.FiniteGroups.Stabilization.DeckDispatch
import Holant.Proofs.FiniteGroups.Stabilization.MatchingStability
import Holant.Proofs.FiniteGroups.Stabilization.ExactTermination


noncomputable section
namespace Holant.LocalDrafts.FinitePGL2.Stabilization.ResolvingExecution.RetainedBranches
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
variable {L κ : Type*} [Field L] [NumberField L] [DecidableEq κ]
variable {m : ℕ} (s : Node L κ) (f : Signature L (m+2))

abbrev augmented := fullRetainedDeck s.family s.torsion f

def minimum : MinimumCore (augmented s f) :=
  Classical.choice (exists_minimumCore (augmented s f)
    ⟨s.core.signature, fullRetainedDeck_retains s.family s.torsion f s.core.retained,
      s.core.prime, s.core.nonbinary⟩)

/-- Keep the original frozen keys and queue while recomputing the family,
complete group and minimum core; a later outer restart may regenerate them. -/
def successor (hτ : ResidualTorsion (augmented s f)) : Node L κ where
  family := augmented s f
  finite := fullRetainedDeck_finite s.family s.finite s.torsion f
  equality := fullRetainedDeck_retains s.family s.torsion f s.equality
  torsion := hτ
  core := minimum s f
  frozen := s.frozen
  queue := s.queue

theorem retained (hτ : ResidualTorsion (augmented s f)) :
    s.family ⊆ (successor s f hτ).family := fullRetainedDeck_retains s.family s.torsion f

theorem arity_nonincrease : (minimum s f).signature.1 ≤ s.core.signature.1 :=
  MinimumCore.arity_nonincrease (fullRetainedDeck_retains s.family s.torsion f) s.core (minimum s f)

inductive Outcome : Type _
  | unary (u : Signature L 1) (retained : (⟨1,u⟩ : AnySignature L) ∈ augmented s f)
      (nonzero : u ≠ 0)
  | infinite (B : Binary (K:=L)) (actual : ActualNonsingular (augmented s f) B)
      (infiniteOrder : ¬ ProjectivelyFinite (transfer B))
  | outer (hτ : ResidualTorsion (augmented s f))
      (step : Node.Step (successor s f hτ) s)
  | unchanged (hτ : ResidualTorsion (augmented s f))
      (group : completeGroup (augmented s f) hτ = completeGroup s.family s.torsion)
      (arity : (minimum s f).signature.1 = s.core.signature.1)
      (noUnary : ¬ RetainedUnary (augmented s f))
      (matching : ∀ g ∈ rawDeck s.family s.torsion f,
        MatchingOrZero (actualTransfers (augmented s f)) g)

/-- No supplied executor, coverage oracle, new minimum core or strictness
hypothesis. Each finite-group branch uses the constructed actual successor. -/
def dispatch (hm : 2 ≤ m) (hcore : s.core.signature = ⟨m+2,f⟩) : Outcome s f := by
  classical
  by_cases hu : RetainedUnary (augmented s f)
  · exact .unary (Classical.choose hu) (Classical.choose_spec hu).1 (Classical.choose_spec hu).2
  · by_cases hτ : ResidualTorsion (augmented s f)
    · by_cases hg : completeGroup (augmented s f) hτ = completeGroup s.family s.torsion
      · by_cases ha : (minimum s f).signature.1 < s.core.signature.1
        · exact .outer hτ (.arity s _ (retained s f hτ) hg ha)
        have ha : (minimum s f).signature.1 = s.core.signature.1 :=
          le_antisymm (arity_nonincrease s f) (Nat.le_of_not_gt ha)
        refine .unchanged hτ hg ha hu ?_
        apply fullRetainedDeck_matching hm s.family s.torsion f (minimum s f) _ hu
        have hn := congrArg Sigma.fst hcore
        change s.core.signature.1 = m+2 at hn
        change (minimum s f).signature.1 = s.core.signature.1 at ha
        omega
      · exact .outer hτ (.group s _ (retained s f hτ)
          (lt_of_le_of_ne (completeGroup_mono (retained s f hτ) s.torsion hτ)
            (fun he => hg he.symm)))
    · have hi := (residual_or_actual_infinite (augmented s f)).resolve_left hτ
      exact .infinite (Classical.choose hi) (Classical.choose_spec hi).1 (Classical.choose_spec hi).2

theorem outer_strict (hτ : ResidualTorsion (augmented s f))
    (h : Node.Step (successor s f hτ) s) :
    Node.RankLT (successor s f hτ).sourceOmega s.sourceOmega := Node.source_step_decreases h

/-- At the unchanged group/core branch, actual old-token work gives the
required continuing Step while retaining the full new family. No arbitrary
same-stratum family change is counted as progress. -/
theorem unchanged_work (hτ : ResidualTorsion (augmented s f))
    (hg : completeGroup (augmented s f) hτ = completeGroup s.family s.torsion)
    (ha : (minimum s f).signature.1 = s.core.signature.1)
    (q : FrozenQueue L s.frozen) (hq : FrozenQueue.Step q s.queue) :
    Node.Step ((successor s f hτ).withQueue q) s ∧
      Node.RankLT ((successor s f hτ).withQueue q).sourceOmega s.sourceOmega := by
  have h : Node.Step ((successor s f hτ).withQueue q) s :=
    .retainedLocal s _ (retained s f hτ) hg ha rfl hq
  exact ⟨h, Node.source_step_decreases h⟩

/-- The stronger conclusion available with the actual saturation invariant
still concerns the frozen complete deck, not all signatures of the family. -/
theorem unchanged_representative_matching (hm : 2 ≤ m)
    (hcore : s.core.signature = ⟨m+2,f⟩) (hsat : FactorSaturated s.family)
    (hτ : ResidualTorsion (augmented s f))
    (hg : completeGroup (augmented s f) hτ = completeGroup s.family s.torsion)
    (ha : (minimum s f).signature.1 = s.core.signature.1)
    (hu : ¬ RetainedUnary (augmented s f)) :
    ∀ g ∈ rawDeck s.family s.torsion f,
      g = 0 ∨ RepresentativeMatching (augmented s f) hτ g :=
  (unchanged_fullRetainedDeck_stable hm s.family s.finite hsat s.torsion f
    s.core hcore (minimum s f) ha hτ hg hu).2.2.2.2.2

end Holant.LocalDrafts.FinitePGL2.Stabilization.ResolvingExecution.RetainedBranches
