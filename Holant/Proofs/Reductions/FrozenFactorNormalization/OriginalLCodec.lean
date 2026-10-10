import Holant.Proofs.Reductions.FrozenFactorNormalization.PaletteCodec


noncomputable section
namespace Holant.LocalDrafts.Hardness.FrozenFactorNormalization.OriginalLCodec
open Holant.Tractable
open Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open GeneralExtraction
variable {L : Type} [Field L] [NumberField L] (φ : L →ₐ[ℚ] AlgebraicComplex)
variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature L (a i.val))
def mapped (i : Fin s) : Signature AlgebraicComplex (a i.val) := RH.mapSignature φ.toRingHom (G i)
abbrev coefficientField := GeneralOriginalTarget.originalField (mapped φ G)
abbrev coefficientPresentation := GeneralOriginalTarget.originalPresentation (mapped φ G)
abbrev presentation := FixedField.ofFiniteDimensional L
def tables : ExactSignatureTables (Module.finrank ℚ L) s 1 a :=
  GeneralFieldReduction.targetTables (presentation (L:=L)) G
def value := (tables G).evaluate (presentation (L:=L))

theorem field_le : coefficientField φ G ≤ φ.fieldRange := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  exact ⟨G i x,rfl⟩
def intoL : coefficientField φ G →ₐ[ℚ] L :=
  φ.equivFieldRange.symm.toAlgHom.comp (IntermediateField.inclusion (field_le φ G))
theorem intoL_value (z : coefficientField φ G) : φ (intoL φ G z) = (z : AlgebraicComplex) := by
  have he := congrArg (fun w : φ.fieldRange => (w : AlgebraicComplex))
    (φ.equivFieldRange.apply_symm_apply (IntermediateField.inclusion (field_le φ G) z))
  exact he
theorem degree_bound : Module.finrank ℚ (coefficientField φ G) ≤ Module.finrank ℚ L :=
  LinearMap.finrank_le_finrank_of_injective (f := (intoL φ G).toLinearMap) (intoL φ G).injective

theorem mapped_tables : TableFieldTransport.mapTables (coefficientPresentation φ G)
    (presentation (L:=L)) (intoL φ G) (GeneralOriginalTarget.originalTables (mapped φ G)) = tables G := by
  unfold TableFieldTransport.mapTables GeneralOriginalTarget.originalTables tables
    GeneralFieldReduction.targetTables
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables
  congr 1
  · funext i x
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    apply φ.injective
    exact intoL_value φ G _
  · funext i x y
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    cases x <;> cases y <;> simp [Signature.disequality]

def toCoefficient : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 a) (presentation (L:=L)).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (coefficientPresentation φ G).encoding
    (value G) (GeneralOriginalTarget.originalValue (mapped φ G)) := by
  have M := TableFieldTransport.toOriginal (coefficientPresentation φ G) (presentation (L:=L))
    (intoL φ G) (GeneralOriginalTarget.originalTables (mapped φ G))
  rw [mapped_tables] at M
  exact M
def fromCoefficient : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 a) (coefficientPresentation φ G).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (presentation (L:=L)).encoding
    (GeneralOriginalTarget.originalValue (mapped φ G)) (value G) := by
  have M := TableFieldTransport.fromOriginal (coefficientPresentation φ G) (presentation (L:=L))
    (intoL φ G) (GeneralOriginalTarget.originalTables (mapped φ G))
  rw [mapped_tables] at M
  exact M

end Holant.LocalDrafts.Hardness.FrozenFactorNormalization.OriginalLCodec
