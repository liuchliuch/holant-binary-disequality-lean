import Holant.Proofs.Closure.OccurrenceCurrent

/-! A retained augmentation cannot promote a higher nonminimum prime to a
minimum while keeping a lower nonbinary prime. Physical batch preparation and
local classification consequently require their real nonminimum context. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceMinimumScope
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization

/-- The actual minimum inequality rules out any higher alleged minimum. -/
theorem lower_retained_prime_prevents_higher_minimum {L : Type*} [Field L]
    (F : SignatureFamily L) (lower higher : AnySignature L)
    (retained : lower ∈ F) (prime : Prime lower) (nonbinary : 3 ≤ lower.1)
    (strict : lower.1 < higher.1) :
    ¬ ∃ minimum : MinimumCore F, minimum.signature = higher := by
  rintro ⟨minimum, literal⟩
  have bound := minimum.minimum lower retained prime nonbinary
  rw [literal] at bound
  exact (not_le_of_gt strict) bound

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- Keeping a real lower minimum prevents every retained higher saved prime
from becoming a minimum in the new physical palette. No arity-only preparation
can supply the `Preparation.actualMinimum` receipt. -/
theorem retained_augmentation_cannot_promote_higher_occurrence
    (before after : Palette G) (retains : before.family ⊆ after.family)
    (lower : MinimumCore before.family) (o : CurrentOccurrences.Id G before)
    (strict : lower.signature.1 < (CurrentOccurrences.savedLeaf G before o).1.1) :
    ¬ ∃ minimum : MinimumCore after.family,
      minimum.signature = (CurrentOccurrences.savedLeaf G before o).1 :=
  lower_retained_prime_prevents_higher_minimum after.family lower.signature
    (CurrentOccurrences.savedLeaf G before o).1 (retains lower.retained)
    lower.prime lower.nonbinary strict

end Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceMinimumScope
end
