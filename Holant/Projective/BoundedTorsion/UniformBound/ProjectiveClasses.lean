import Holant.Projective.BoundedTorsion.PGL
import Mathlib.Data.Set.Card

/-! Cardinal bounds pass from normalized lifts to the original projective
classes, and then to the genuine subgroup of PGL₂. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {K E : Type*} [Field K] [Field E]

/-- Scalar descent transfers the cardinal bound on lifts to projective classes
in the original field. -/
theorem ncard_projective_image_le_of_lifts (f : K →+* E)
    {G : Set (Binary (K := K))} {S : Set (Binary (K := E))}
    (hS : S.Finite) (hne : ∀ T ∈ G, T ≠ 0)
    (hlift : ∀ T ∈ G, ∃ U ∈ S, ∃ c : E, c ≠ 0 ∧ U = c • T.map f) :
    (projectiveClass '' G).ncard ≤ S.ncard := by
  calc
    (projectiveClass '' G).ncard ≤ (projectiveClass '' S).ncard := by
      apply Set.ncard_le_ncard_of_injOn (extendProjectiveClass f) _ _ (hS.image _)
      · rintro _ ⟨T, hT, rfl⟩
        obtain ⟨U, hU, c, hc, rfl⟩ := hlift T hT
        exact ⟨c • T.map f, hU, projectiveClass_smul _ hc⟩
      · rintro _ ⟨T, hT, rfl⟩ _ ⟨U, hU, rfl⟩ heq
        exact projectiveClass_map_injective f (hne U hU) heq
    _ ≤ S.ncard := Set.ncard_image_le hS

/-- The actual PGL subgroup and its literal projective image have equal size. -/
theorem card_projectiveSubgroup_eq {G : Set (Binary (K := K))}
    (hG : ProjectiveMatrixGroup G) :
    Nat.card (projectiveSubgroup hG) = (projectiveClass '' G).ncard := by
  rw [← projectiveSubgroup_image hG,
    Set.ncard_image_of_injective _ pglToProjectiveClass_injective]
  rfl

end
end Holant.Projective.BoundedTorsion
