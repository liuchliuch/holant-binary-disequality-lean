import Holant.Proofs.Algorithms.FamilyFieldInclusion
import Holant.Proofs.Algorithms.TableFieldTransport
import Holant.Complexity.FixedGadgetSubstitution.PresentedScaledFamily


namespace Holant.LocalDrafts.MainChain.CommonFieldTables
open Computability Holant.Algebraic Holant.Complexity
open Holant.Complexity.ExactSignatureTables
open Holant.Complexity.FixedGadgetSubstitution
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {L B : Type} [Field L] [Algebra ℚ L] [Fintype B]
    {s b : ℕ} {arity : ℕ → ℕ}
    (coeff : CoefficientIndex s b arity → L) (extra : B → L)
    (hc : ∀ a, IsAlgebraic ℚ (coeff a)) (he : ∀ a, IsAlgebraic ℚ (extra a))

abbrev combined := FamilyFieldInclusion.combined coeff extra
abbrev originalPresentation := familyPresentation coeff hc
abbrev commonPresentation := FamilyFieldInclusion.commonPresentation coeff extra hc he
abbrev embedding := FamilyFieldInclusion.embedding coeff extra
abbrev originalTables := PresentedScaledFamily.tables coeff hc id
abbrev commonTables := PresentedScaledFamily.tables (combined coeff extra)
  (FamilyFieldInclusion.combined_algebraic coeff extra hc he) Sum.inl

theorem mapped_coefficient (i : CoefficientIndex s b arity) :
    (commonPresentation coeff extra hc he).decode.symm
      (embedding coeff extra ((originalPresentation coeff hc).decode
        (familyCoordinates coeff hc i))) =
    familyCoordinates (combined coeff extra)
      (FamilyFieldInclusion.combined_algebraic coeff extra hc he) (.inl i) := by
  apply (commonPresentation coeff extra hc he).decode.injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (familyCoordinates_spec coeff hc i).trans
    (familyCoordinates_spec (combined coeff extra)
      (FamilyFieldInclusion.combined_algebraic coeff extra hc he) (.inl i)).symm

/-- The generated rational coefficient tables, not just their ambient
denotations, agree under the proved fixed-field embedding. -/
theorem map_tables_eq :
    TableFieldTransport.mapTables (originalPresentation coeff hc)
      (commonPresentation coeff extra hc he) (embedding coeff extra)
      (originalTables coeff hc) = commonTables coeff extra hc he := by
  unfold TableFieldTransport.mapTables originalTables commonTables PresentedScaledFamily.tables
  congr 1
  · funext i x
    exact mapped_coefficient coeff extra hc he (.inl ⟨i,x⟩)
  · funext i x y
    exact mapped_coefficient coeff extra hc he (.inr (i,x,y))

abbrev originalValue := (originalTables coeff hc).evaluate (originalPresentation coeff hc)
abbrev commonValue := (commonTables coeff extra hc he).evaluate
  (commonPresentation coeff extra hc he)

theorem value_embedding (r : Input s b arity) :
    commonValue coeff extra hc he r = embedding coeff extra (originalValue coeff hc r) := by
  rw [commonValue, ← map_tables_eq]
  exact TableFieldTransport.evaluate_map _ _ _ _ r

/-- Remove the enlarged answer codec from the target end of a construction. -/
def toOriginal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s b arity) (commonPresentation coeff extra hc he).encoding
    (RawClosedNetwork.validatedEncoding s b arity) (originalPresentation coeff hc).encoding
    (commonValue coeff extra hc he) (originalValue coeff hc) := by
  have r := TableFieldTransport.toOriginal (originalPresentation coeff hc)
    (commonPresentation coeff extra hc he) (embedding coeff extra) (originalTables coeff hc)
  rw [map_tables_eq] at r
  exact r

def fromOriginal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s b arity) (originalPresentation coeff hc).encoding
    (RawClosedNetwork.validatedEncoding s b arity) (commonPresentation coeff extra hc he).encoding
    (originalValue coeff hc) (commonValue coeff extra hc he) := by
  have r := TableFieldTransport.fromOriginal (originalPresentation coeff hc)
    (commonPresentation coeff extra hc he) (embedding coeff extra) (originalTables coeff hc)
  rw [map_tables_eq] at r
  exact r

end
end Holant.LocalDrafts.MainChain.CommonFieldTables
