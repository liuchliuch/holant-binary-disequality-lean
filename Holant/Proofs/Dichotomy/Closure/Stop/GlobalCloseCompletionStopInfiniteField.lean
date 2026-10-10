import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopInfiniteSpectral

/-! Preserve query/output word control across the spectral field boundary.
The chosen rank-one H belongs to the literal source coefficient field; its
actual interpolation runs through the unchanged current palette and then
through that palette's existing original-G interpreter. No PolyTime-only
composition or identification of unrelated rational bases is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteField
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose Holant.Complexity.BinaryInterpolation Holant.Complexity.UniversalPairReduction
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure hiding binarySignature
open Holant.LocalDrafts.BinaryInterpolation Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open GlobalCloseCompletionStopInfiniteSpectral
namespace SO
export SingularExtraction.Composition.OriginalField (field presentation tables value encoding)
end SO
namespace CO
export SingularExtraction.Composition.CanonicalOracle (encoding value presentation fieldEquiv value_equiv)
end CO
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (B : Binary (K:=OI.K G)) (actual : ActualNonsingular P.family B)
variable (infinite : ¬ProjectivelyFinite (transfer B))

abbrev complexFamily := SourceTransport.family (mapped G P)
abbrev commonField := FieldSource.Field (complexFamily G P) (spectralMacro G P B actual infinite)
  (pencil G P B actual infinite)
abbrev commonPresentation := FieldSource.fixedField (complexFamily G P)
  (SourceTransport.family_algebraic (mapped G P)) (spectralMacro G P B actual infinite) (pencil G P B actual infinite)
abbrev commonAdjoined := BinaryFamily.signatures
  (AlgebraicSource.CommonField.original (complexFamily G P) (spectralMacro G P B actual infinite).binary
    (pencil G P B actual infinite))
  (AlgebraicSource.CommonField.right (complexFamily G P) (spectralMacro G P B actual infinite).binary
    (pencil G P B actual infinite))

theorem common_entry (i : Fin (P.count+1)) (z : Fin (extendedArity P.count P.arity i.val)→Bool) :
    (commonAdjoined G P B actual infinite i z : ℂ)=
      SourceTransport.inclusion (adjoined G P B actual infinite i z) := by
  by_cases hi : i.val<P.count
  · simp [commonAdjoined,adjoined,BinaryFamily.signatures,hi,complexFamily,SourceTransport.family]
  · simp [commonAdjoined,adjoined,BinaryFamily.signatures,hi,H,SourceTransport.inclusion]
    rfl

theorem source_field_le : SO.field (adjoined G P B actual infinite)≤
    (commonField G P B actual infinite).comap (algebraicClosure ℚ ℂ).val := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  change SourceTransport.inclusion (adjoined G P B actual infinite i x)∈commonField G P B actual infinite
  rw [←common_entry G P B actual infinite i x]
  exact (commonAdjoined G P B actual infinite i x).property

def sourceEmbedding : SO.field (adjoined G P B actual infinite)→ₐ[ℚ] commonField G P B actual infinite where
  toFun z := ⟨(algebraicClosure ℚ ℂ).val (z : AlgebraicComplex),source_field_le G P B actual infinite z.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add _ (x : AlgebraicComplex) (y : AlgebraicComplex))
  map_mul' x y := Subtype.ext (map_mul _ (x : AlgebraicComplex) (y : AlgebraicComplex))
  commutes' q := Subtype.ext ((algebraicClosure ℚ ℂ).val.commutes q)

def commonSourceTables : ExactSignatureTables (Module.finrank ℚ (commonField G P B actual infinite))
    (P.count+1) 1 (extendedArity P.count P.arity) where
  vertex i z := (commonPresentation G P B actual infinite).decode.symm (commonAdjoined G P B actual infinite i z)
  edge _ i j := (commonPresentation G P B actual infinite).decode.symm (Signature.disequality i j)

theorem source_tables : TableFieldTransport.mapTables (SO.presentation (adjoined G P B actual infinite))
    (commonPresentation G P B actual infinite) (sourceEmbedding G P B actual infinite)
    (SO.tables (adjoined G P B actual infinite))=commonSourceTables G P B actual infinite := by
  unfold TableFieldTransport.mapTables SingularExtraction.Composition.OriginalField.tables commonSourceTables
  congr 1
  · funext i z
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    apply Subtype.ext
    exact (common_entry G P B actual infinite i z).symm
  · funext i j k
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    apply Subtype.ext
    cases j <;> cases k <;> simp [sourceEmbedding,Signature.disequality]

theorem common_source_value :
    (commonSourceTables G P B actual infinite).evaluate (commonPresentation G P B actual infinite)=
      AlgebraicSource.CommonField.sourceValue (complexFamily G P) (spectralMacro G P B actual infinite).binary
        (pencil G P B actual infinite) := by
  funext r
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [commonSourceTables,LinearEquiv.apply_symm_apply]
  rfl

def sourceAdapter : LengthControlledOracleReduction
    (FieldSource.inputEncoding (s:=P.count) (arity:=P.arity)) (SO.encoding (adjoined G P B actual infinite))
    (FieldSource.inputEncoding (s:=P.count) (arity:=P.arity)) (commonPresentation G P B actual infinite).encoding
    (SO.value (adjoined G P B actual infinite))
    (AlgebraicSource.CommonField.sourceValue (complexFamily G P) (spectralMacro G P B actual infinite).binary
      (pencil G P B actual infinite)) := by
  have h := TableFieldTransport.fromOriginal (SO.presentation (adjoined G P B actual infinite))
    (commonPresentation G P B actual infinite) (sourceEmbedding G P B actual infinite)
    (SO.tables (adjoined G P B actual infinite))
  rw [source_tables,common_source_value] at h
  exact h

/-- Physical fixed-matrix conversion back from the complex canonical answer
codec into the actual algebraic source coefficient field. -/
def canonicalBack : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (CO.encoding (mapped G P))
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (SO.encoding (mapped G P))
    (CO.value (mapped G P)) (SO.value (mapped G P)) :=
  controlledOneQueryOfEq (identityComputes (RawClosedNetwork.validatedEncoding P.count 1 P.arity))
    (FieldCodec.computes (SO.presentation (mapped G P)) (CO.presentation (mapped G P))
      (CO.fieldEquiv (mapped G P)).toLinearMap)
    ((SO.tables (mapped G P)).outputBound (SO.presentation (mapped G P)))
    (CO.value (mapped G P)) (CO.value_equiv (mapped G P))

/-- Γ,H → original G, with every intermediate stage still length-controlled.
Both the current-palette programme and original answer codec remain literal. -/
def toOriginal : LengthControlledOracleReduction
    (FieldSource.inputEncoding (s:=P.count) (arity:=P.arity)) (SO.encoding (adjoined G P B actual infinite))
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (SO.value (adjoined G P B actual infinite)) (OriginalForestSource.value G) :=
  Programme.compose (sourceAdapter G P B actual infinite)
    (Programme.compose
      (UnifiedSource.OriginalInterpolation.controlled (complexFamily G P)
        (SourceTransport.family_algebraic (mapped G P)) (spectralMacro G P B actual infinite)
        (pencil G P B actual infinite))
      (Programme.compose (canonicalBack G P)
        (Programme.compose (OriginalLCodec.fromCoefficient (StableHigherCurrentPurePinsCore.embedding G) P.table)
          P.toOriginal.controlled)))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteField
end
