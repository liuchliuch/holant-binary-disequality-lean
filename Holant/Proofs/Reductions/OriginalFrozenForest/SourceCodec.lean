import Holant.Proofs.Reductions.OriginalFrozenForest.Palette
import Holant.Proofs.Reductions.RootPreprocessing.BoundaryLaws


noncomputable section
namespace Holant.LocalDrafts.Hardness.OriginalFrozenForest
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FrozenFactorNormalization
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
variable {L : Type} [Field L] [NumberField L] (φ : L →ₐ[ℚ] AlgebraicComplex)
variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature L (a i.val))

abbrev originalEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev originalPresentation := OriginalLCodec.presentation (L:=L)
abbrev originalValue := OriginalLCodec.value G
abbrev sourceField := RootPreprocessing.sourceField (embedded φ G)
abbrev sourcePresentation := RootPreprocessing.sourcePresentation (embedded φ G)
abbrev sourceValue := RootPreprocessing.sourceValue (embedded φ G)

theorem source_field_le : sourceField φ G ≤ φ.fieldRange := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨i,rfl⟩
  rcases i with ⟨j,x⟩ | ⟨j,u,v⟩
  · exact ⟨G j x,rfl⟩
  · refine ⟨Signature.disequality (K:=L) u v,?_⟩
    cases u <;> cases v <;> simp [RootPreprocessing.sourceCoefficient,OriginalFamily.coefficient,
      RootPreprocessing.nativeX,Signature.disequality]
def sourceIntoL : sourceField φ G →ₐ[ℚ] L :=
  φ.equivFieldRange.symm.toAlgHom.comp (IntermediateField.inclusion (source_field_le φ G))
theorem sourceIntoL_exact (x : sourceField φ G) : φ (sourceIntoL φ G x)=(x : AlgebraicComplex) :=
  congrArg (fun z : φ.fieldRange => (z : AlgebraicComplex))
    (φ.equivFieldRange.apply_symm_apply (IntermediateField.inclusion (source_field_le φ G) x))

theorem original_exact (r : ExactSignatureTables.Input s 1 a) :
    φ (originalValue G r) = RootPreprocessing.ambientValue (embedded φ G) r := by
  have hm : (r.val.realize r.property G (fun _ => Signature.disequality)).map φ.toRingHom =
      r.val.realize r.property (embedded φ G) (RootPreprocessing.nativeX) := by
    unfold Network.map RawClosedNetwork.realize
    congr 1
    funext e u v
    cases u <;> cases v <;> simp [RootPreprocessing.nativeX,Signature.disequality]
  change φ ((FieldReduction.targetTables (originalPresentation (L:=L)) G).evaluate
    (originalPresentation (L:=L)) r) = _
  rw [FieldReduction.target_evaluate]
  change φ.toRingHom ((r.val.realize r.property G (fun _ => Signature.disequality)).denote Fin.elim0) = _
  rw [←Network.denote_map φ.toRingHom,hm]
  rfl

theorem source_value_in_L (r : ExactSignatureTables.Input s 1 a) :
    sourceIntoL φ G (sourceValue φ G r)=originalValue G r := by
  apply φ.injective
  change φ (sourceIntoL φ G (sourceValue φ G r)) = φ (originalValue G r)
  rw [sourceIntoL_exact,RootPreprocessing.source_exact,original_exact]

def originalToSource : LengthControlledOracleReduction
    (originalEncoding (s:=s) (a:=a)) (originalPresentation (L:=L)).encoding
    (originalEncoding (s:=s) (a:=a)) (sourcePresentation φ G).encoding
    (originalValue G) (sourceValue φ G) :=
  controlledOneQueryOfEq (identityComputes (originalEncoding (s:=s) (a:=a)))
    (FieldCodec.computes (sourcePresentation φ G) (originalPresentation (L:=L)) (sourceIntoL φ G).toLinearMap)
    ((RootPreprocessing.sourceTables (embedded φ G)).outputBound (sourcePresentation φ G))
    (originalValue G) (fun r => (source_value_in_L φ G r).symm)
def sourceToOriginal : LengthControlledOracleReduction
    (originalEncoding (s:=s) (a:=a)) (sourcePresentation φ G).encoding
    (originalEncoding (s:=s) (a:=a)) (originalPresentation (L:=L)).encoding
    (sourceValue φ G) (originalValue G) :=
  controlledOneQueryOfEq (identityComputes (originalEncoding (s:=s) (a:=a)))
    (FieldCodec.retractComputes (sourcePresentation φ G) (originalPresentation (L:=L)) (sourceIntoL φ G))
    ((OriginalLCodec.tables G).outputBound (originalPresentation (L:=L)))
    (sourceValue φ G) (fun r => by
      change sourceValue φ G r = (sourceIntoL φ G).toLinearMap.leftInverse (originalValue G r)
      rw [←source_value_in_L φ G r]
      exact (FieldCodec.retract_embedding (sourceIntoL φ G) (sourceValue φ G r)).symm)

theorem original_zero (hI : RetainsIdentity (Set.range (fun i =>
      (⟨a i.val,embedded φ G i⟩ : AnySignature AlgebraicComplex))))
    (r : ExactSignatureTables.Input s 1 a) (h : ¬ RootPreprocessing.Clean (embedded φ G) r.val) :
    originalValue G r=0 := by
  rw [←source_value_in_L φ G r]
  change sourceIntoL φ G (RootPreprocessing.sourceValue (embedded φ G) r) = 0
  rw [RootPreprocessing.zero_recovery (embedded φ G) hI r h,map_zero]
theorem original_nullary (r : ExactSignatureTables.Input s 1 a)
    (h : ∀ row ∈ r.val.vertices, a row.1=0) :
    originalValue G r=sourceIntoL φ G (RootPreprocessing.context (embedded φ G) r) := by
  rw [←source_value_in_L φ G r]
  change sourceIntoL φ G (RootPreprocessing.sourceValue (embedded φ G) r) = _
  rw [RootPreprocessing.nullary_value (embedded φ G) r h]
include φ in
theorem original_empty : originalValue G (RootPreprocessing.emptyInput (s:=s) (a:=a))=1 := by
  rw [←source_value_in_L φ G]
  change sourceIntoL φ G (RootPreprocessing.sourceValue (embedded φ G) RootPreprocessing.emptyInput) = 1
  rw [RootPreprocessing.empty_value,map_one]

end Holant.LocalDrafts.Hardness.OriginalFrozenForest
