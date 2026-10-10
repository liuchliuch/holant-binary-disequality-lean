import Holant.Projective.BoundedTorsion.UniformBound


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure

noncomputable section
variable {L : Type*} [Field L]

def ResidualTorsion (F : SignatureFamily L) : Prop :=
  ∀ B, ActualNonsingular F B → ProjectivelyFinite (transfer B)

theorem nativeX_actual (F : SignatureFamily L) : ActualNonsingular F (X : Binary (K := L)) := by
  refine ⟨?_, det_X_ne_zero⟩
  exact Gadget.realizes_edgeBox (K := L) F .disequality

/-- The native X edge already supplies the identity transfer; the empty family
does not require a fictitious supplied binary to make its transfer set nonempty. -/
theorem actualTransfers_nonempty (F : SignatureFamily L) : (actualTransfers F).Nonempty := by
  exact ⟨transfer X, X, nativeX_actual F, 1, one_ne_zero, (one_smul L _).symm⟩

def completeGroup (F : SignatureFamily L) (hτ : ResidualTorsion F) : Subgroup (PGL2 L) :=
  projectiveSubgroup (actualTransfers_projectiveMatrixGroup F (actualTransfers_nonempty F) hτ)

theorem completeGroup_image (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    pglToProjectiveClass '' (completeGroup F hτ : Set (PGL2 L)) =
      projectiveClass '' actualTransfers F :=
  projectiveSubgroup_image _

theorem actualTransfers_mono {F G : SignatureFamily L} (hFG : F ⊆ G) :
    actualTransfers F ⊆ actualTransfers G := by
  rintro T ⟨B, hB, c, hc, he⟩
  exact ⟨B, ⟨hB.1.mono hFG, hB.2⟩, c, hc, he⟩

theorem completeGroup_mono {F G : SignatureFamily L} (hFG : F ⊆ G)
    (hF : ResidualTorsion F) (hG : ResidualTorsion G) :
    completeGroup F hF ≤ completeGroup G hG := by
  rintro q ⟨U, hU, rfl⟩
  exact ⟨U, actualTransfers_mono hFG hU, rfl⟩

/-- A genuinely new actual transfer class forces strict inclusion. -/
theorem completeGroup_lt_of_new_class {F G : SignatureFamily L} (hFG : F ⊆ G)
    (hF : ResidualTorsion F) (hG : ResidualTorsion G)
    (U : Matrix.GeneralLinearGroup Bool L) (hU : (U : Binary) ∈ actualTransfers G)
    (hnew : pglMk L U ∉ completeGroup F hF) :
    completeGroup F hF < completeGroup G hG := by
  refine lt_of_le_of_ne (completeGroup_mono hFG hF hG) ?_
  intro he
  exact hnew (he.symm ▸ (show pglMk L U ∈ completeGroup G hG from ⟨U, hU, rfl⟩))

variable [NumberField L]

theorem completeGroup_finite (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    Finite (completeGroup F hτ) :=
  finite_projectiveSubgroup _ (bounded_torsion F (actualTransfers_nonempty F) hτ).2

theorem completeGroup_card_le (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    Nat.card (completeGroup F hτ) ≤ uniformProjectiveBound (Module.finrank ℚ L) := by
  exact card_projectiveSubgroup_le_uniformBound _ (by
    rintro T ⟨B, hB, c, hc, rfl⟩
    exact (hτ B hB).smul hc)

/-- This is an actual decreasing group coordinate, with its upper bound proved
over one frozen number field.  It is a coarser bound than the source's M_L. -/
def groupDefect (F : SignatureFamily L) (hτ : ResidualTorsion F) : ℕ :=
  uniformProjectiveBound (Module.finrank ℚ L) - Nat.card (completeGroup F hτ)

theorem groupDefect_lt_of_strict {F G : SignatureFamily L}
    (hF : ResidualTorsion F) (hG : ResidualTorsion G)
    (h : completeGroup F hF < completeGroup G hG) :
    groupDefect G hG < groupDefect F hF := by
  letI := completeGroup_finite G hG
  have hc := Subgroup.card_lt_of_lt h
  have hb := completeGroup_card_le G hG
  unfold groupDefect
  omega

/-- No assertion that a changed family is a strict successor: if no new
actual transfer class appears, the complete group remains exactly equal. -/
theorem completeGroup_eq_or_lt {F G : SignatureFamily L} (hFG : F ⊆ G)
    (hF : ResidualTorsion F) (hG : ResidualTorsion G) :
    completeGroup F hF = completeGroup G hG ∨
      completeGroup F hF < completeGroup G hG :=
  eq_or_lt_of_le (completeGroup_mono hFG hF hG)

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
