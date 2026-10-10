import Holant.Proofs.FiniteGroups.Stabilization.ActualGroups


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
attribute [local instance] Classical.propDecidable
variable {L : Type*} [Field L]

theorem exists_actual_representative (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (q : completeGroup F hτ) :
    ∃ B, ActualNonsingular F B ∧
      projectiveClass (transfer B) = pglToProjectiveClass q.1 := by
  have hq : pglToProjectiveClass q.1 ∈ projectiveClass '' actualTransfers F := by
    rw [← completeGroup_image F hτ]
    exact ⟨q.1, q.2, rfl⟩
  obtain ⟨T, ⟨B, hB, c, hc, rfl⟩, he⟩ := hq
  rw [projectiveClass_smul _ hc] at he
  exact ⟨B, hB, he⟩

def actualRepresentative (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (q : completeGroup F hτ) : Binary (K := L) :=
  if q = 1 then X else (exists_actual_representative F hτ q).choose

@[simp] theorem actualRepresentative_one (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    actualRepresentative F hτ 1 = X := by simp [actualRepresentative]

@[simp] theorem actualRepresentative_identity_transfer (F : SignatureFamily L)
    (hτ : ResidualTorsion F) : transfer (actualRepresentative F hτ 1) = 1 := by
  rw [actualRepresentative_one, transfer, X_mul_X]

theorem actualRepresentative_actual (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (q : completeGroup F hτ) : ActualNonsingular F (actualRepresentative F hτ q) := by
  by_cases h : q = 1
  · simpa [actualRepresentative, h] using nativeX_actual F
  · simpa only [actualRepresentative, if_neg h] using
      (exists_actual_representative F hτ q).choose_spec.1

theorem actualRepresentative_class (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (q : completeGroup F hτ) :
    projectiveClass (transfer (actualRepresentative F hτ q)) = pglToProjectiveClass q.1 := by
  by_cases h : q = 1
  · subst q
    rw [actualRepresentative_identity_transfer]
    exact (pglToProjectiveClass_mk (1 : Matrix.GeneralLinearGroup Bool L)).symm
  · simpa only [actualRepresentative, if_neg h] using
      (exists_actual_representative F hτ q).choose_spec.2

theorem actualRepresentative_injective (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    Function.Injective (actualRepresentative F hτ) := by
  intro q r h
  apply Subtype.ext
  apply pglToProjectiveClass_injective
  rw [← actualRepresentative_class F hτ q, ← actualRepresentative_class F hτ r, h]

theorem actualRepresentative_covers (F : SignatureFamily L) (hτ : ResidualTorsion F)
    {B : Binary (K := L)} (hB : ActualNonsingular F B) :
    ∃ q : completeGroup F hτ,
      projectiveClass (transfer (actualRepresentative F hτ q)) = projectiveClass (transfer B) := by
  have ht : transfer B ∈ actualTransfers F := ⟨B, hB, 1, one_ne_zero, (one_smul L _).symm⟩
  have hp : projectiveClass (transfer B) ∈
      pglToProjectiveClass '' (completeGroup F hτ : Set (PGL2 L)) := by
    rw [completeGroup_image]
    exact ⟨transfer B, ht, rfl⟩
  obtain ⟨q, hq, he⟩ := hp
  exact ⟨⟨q, hq⟩, (actualRepresentative_class F hτ ⟨q, hq⟩).trans he⟩

theorem actualRepresentatives_finite [NumberField L] (F : SignatureFamily L)
    (hτ : ResidualTorsion F) : (Set.range (actualRepresentative F hτ)).Finite := by
  letI := completeGroup_finite F hτ
  exact Set.finite_range _

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
