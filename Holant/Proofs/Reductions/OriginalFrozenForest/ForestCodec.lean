import Holant.Proofs.Reductions.OriginalFrozenForest.SourceCodec


noncomputable section
namespace Holant.LocalDrafts.Hardness.OriginalFrozenForest
open Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open FactorSaturation FrozenFactorNormalization GeneralExtraction
variable {L : Type} [Field L] [NumberField L] (φ : L →ₐ[ℚ] AlgebraicComplex)
variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature L (a i.val))
variable (hI : Holant.LocalDrafts.FinitePGL2.Stabilization.RetainsIdentity (Set.range (fun i : Fin s =>
  (⟨a i.val,embedded φ G i⟩ : AnySignature AlgebraicComplex))))

abbrev catalogueField : IntermediateField ℚ AlgebraicComplex :=
  GeneralOriginalTarget.originalField (oldTable φ G hI)
abbrev cataloguePresentation := GeneralOriginalTarget.originalPresentation (oldTable φ G hI)
abbrev catalogueValue := GeneralOriginalTarget.originalValue (oldTable φ G hI)
abbrev catalogueEncoding := WholeForest.inputEncoding (roots φ G hI)

theorem catalogue_field_le : catalogueField φ G hI ≤ WholeForest.field (roots φ G hI) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  exact CommonField.vertex_covered (roots φ G hI).signature (roots φ G hI).nonzero (roots φ G hI).identity i x
def catalogueEmbedding : catalogueField φ G hI →ₐ[ℚ] WholeForest.field (roots φ G hI) :=
  IntermediateField.inclusion (catalogue_field_le φ G hI)
theorem catalogue_mapped_tables : TableFieldTransport.mapTables (cataloguePresentation φ G hI)
    (WholeForest.presentation (roots φ G hI)) (catalogueEmbedding φ G hI)
    (GeneralOriginalTarget.originalTables (oldTable φ G hI)) = WholeForest.sourceTables (roots φ G hI) := by
  unfold TableFieldTransport.mapTables GeneralOriginalTarget.originalTables WholeForest.sourceTables
    GeneralFieldReduction.targetTables Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables
  congr 1
  · funext i x
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    apply Subtype.ext
    exact (CommonField.table_exact (roots φ G hI).signature (roots φ G hI).nonzero
      (roots φ G hI).identity i.val i.isLt x).symm
  · funext e u v
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    cases u <;> cases v <;> simp [Signature.disequality]

def catalogueToForest : LengthControlledOracleReduction
    (catalogueEncoding φ G hI) (cataloguePresentation φ G hI).encoding
    (catalogueEncoding φ G hI) (WholeForest.presentation (roots φ G hI)).encoding
    (catalogueValue φ G hI) (WholeForest.sourceValue (roots φ G hI)) := by
  have M : LengthControlledOracleReduction
      (catalogueEncoding φ G hI) (cataloguePresentation φ G hI).encoding
      (catalogueEncoding φ G hI) (WholeForest.presentation (roots φ G hI)).encoding
      (catalogueValue φ G hI)
      ((TableFieldTransport.mapTables (cataloguePresentation φ G hI)
        (WholeForest.presentation (roots φ G hI)) (catalogueEmbedding φ G hI)
        (GeneralOriginalTarget.originalTables (oldTable φ G hI))).evaluate
          (WholeForest.presentation (roots φ G hI))) :=
    TableFieldTransport.fromOriginal (cataloguePresentation φ G hI)
      (WholeForest.presentation (roots φ G hI)) (catalogueEmbedding φ G hI)
      (GeneralOriginalTarget.originalTables (oldTable φ G hI))
  rw [catalogue_mapped_tables φ G hI] at M
  exact M
def forestToCatalogue : LengthControlledOracleReduction
    (catalogueEncoding φ G hI) (WholeForest.presentation (roots φ G hI)).encoding
    (catalogueEncoding φ G hI) (cataloguePresentation φ G hI).encoding
    (WholeForest.sourceValue (roots φ G hI)) (catalogueValue φ G hI) := by
  have M : LengthControlledOracleReduction
      (catalogueEncoding φ G hI) (WholeForest.presentation (roots φ G hI)).encoding
      (catalogueEncoding φ G hI) (cataloguePresentation φ G hI).encoding
      ((TableFieldTransport.mapTables (cataloguePresentation φ G hI)
        (WholeForest.presentation (roots φ G hI)) (catalogueEmbedding φ G hI)
        (GeneralOriginalTarget.originalTables (oldTable φ G hI))).evaluate
          (WholeForest.presentation (roots φ G hI)))
      (catalogueValue φ G hI) :=
    TableFieldTransport.toOriginal (cataloguePresentation φ G hI)
      (WholeForest.presentation (roots φ G hI)) (catalogueEmbedding φ G hI)
      (GeneralOriginalTarget.originalTables (oldTable φ G hI))
  rw [catalogue_mapped_tables φ G hI] at M
  exact M

end Holant.LocalDrafts.Hardness.OriginalFrozenForest
