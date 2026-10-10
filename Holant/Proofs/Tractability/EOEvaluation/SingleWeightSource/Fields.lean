import Holant.Proofs.Tractability.EOEvaluation.SingleWeightSource.Producer
import Holant.Proofs.Reductions.SingleWeightCompletion.AnswerField
import Holant.Complexity.FixedFieldMachines.Concrete


namespace Holant.LocalDrafts.Tractability.EOEvaluation.SingleWeightSource.Fields
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines ExactSignatureTables
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀ i, (⟨arity i.val, G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)
    (h : SingleWeightAlternative (preprocess Gamma))

abbrev completedCoefficient := OriginalFamily.coefficient
  (Producer.completedTable G Gamma hmem h) KSourceTransport.nativeEdges
abbrev completedField := familyField (completedCoefficient G Gamma hmem h)
abbrev completedPresentation := OriginalFamily.presentation
  (Producer.completedTable G Gamma hmem h) KSourceTransport.nativeEdges
abbrev completedValue := OriginalFamily.value
  (Producer.completedTable G Gamma hmem h) KSourceTransport.nativeEdges
abbrev targetCoefficient := OriginalFamily.coefficient
  (Producer.targetTable G Gamma hmem h) KSourceTransport.nativeEdges
abbrev targetField := familyField (targetCoefficient G Gamma hmem h)
abbrev targetPresentation := OriginalFamily.presentation
  (Producer.targetTable G Gamma hmem h) KSourceTransport.nativeEdges
abbrev targetValue := OriginalFamily.value
  (Producer.targetTable G Gamma hmem h) KSourceTransport.nativeEdges

/-- The scalar producer and the prescribed completed presentation retain
the same original entries and actual native-X table. Compare coefficients
without unfolding either chosen basis or any graph machine. -/
private theorem context_coefficient_eq
    (c : CoefficientIndex s 1 (Producer.completedArity G Gamma hmem h)) :
    RootPreprocessing.sourceCoefficient (Producer.completedTable G Gamma hmem h) c =
      completedCoefficient G Gamma hmem h c := by
  rcases c with ⟨i, x⟩ | ⟨i, b, c⟩ <;> rfl

theorem context_le_completed :
    RootPreprocessing.sourceField (Producer.completedTable G Gamma hmem h) ≤
      completedField G Gamma hmem h := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨c, rfl⟩
  change RootPreprocessing.sourceCoefficient (Producer.completedTable G Gamma hmem h) c ∈
    completedField G Gamma hmem h
  rw [context_coefficient_eq]
  exact coefficient_mem_familyField (completedCoefficient G Gamma hmem h) c

def contextInclusion : RootPreprocessing.sourceField (Producer.completedTable G Gamma hmem h) →ₐ[ℚ]
    completedField G Gamma hmem h := IntermediateField.inclusion (context_le_completed G Gamma hmem h)

def contextInclusionComputes : Computes
    (RootPreprocessing.sourcePresentation (Producer.completedTable G Gamma hmem h)).encoding
    (completedPresentation G Gamma hmem h).encoding (contextInclusion G Gamma hmem h) :=
  FieldCodec.computes (RootPreprocessing.sourcePresentation (Producer.completedTable G Gamma hmem h))
    (completedPresentation G Gamma hmem h) (contextInclusion G Gamma hmem h).toLinearMap

theorem target_coefficient_mem
    (c : CoefficientIndex (Producer.count G Gamma hmem h) 1
      (Producer.targetArity G Gamma hmem h)) :
    targetCoefficient G Gamma hmem h c ∈ completedField G Gamma hmem h := by
  rcases c with ⟨j, x⟩ | ⟨j, u, v⟩
  · change RootPreprocessing.targetTable (Producer.completedTable G Gamma hmem h) j x ∈
      completedField G Gamma hmem h
    rw [RootPreprocessing.target_entry (Producer.completedTable G Gamma hmem h) j x]
    exact coefficient_mem_familyField (completedCoefficient G Gamma hmem h)
      (.inl ⟨RootPreprocessing.includeLabel (Producer.completedTable G Gamma hmem h) j,
        fun k => x (Fin.cast
          (RootPreprocessing.target_arity (Producer.completedTable G Gamma hmem h) j).symm k)⟩)
  · exact coefficient_mem_familyField (completedCoefficient G Gamma hmem h) (.inr (j, u, v))

theorem target_le_completed : targetField G Gamma hmem h ≤ completedField G Gamma hmem h := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨c, rfl⟩
  exact target_coefficient_mem G Gamma hmem h c

def targetInclusion : targetField G Gamma hmem h →ₐ[ℚ] completedField G Gamma hmem h :=
  IntermediateField.inclusion (target_le_completed G Gamma hmem h)
def targetInclusionComputes : Computes (targetPresentation G Gamma hmem h).encoding
    (completedPresentation G Gamma hmem h).encoding (targetInclusion G Gamma hmem h) :=
  FieldCodec.computes (targetPresentation G Gamma hmem h) (completedPresentation G Gamma hmem h)
    (targetInclusion G Gamma hmem h).toLinearMap

/-- Proven relation to the old vertex-only endpoint, not a codec identity. -/
theorem native_vertex_le : SingleWeightCompletion.AnswerField.Source (Producer.native G) ≤
    familyField (KSourceTransport.nativeCoefficient G) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨⟨i, x⟩, rfl⟩
  exact coefficient_mem_familyField (KSourceTransport.nativeCoefficient G) (.inl ⟨i, x⟩)

theorem completed_coefficient_mem
    (c : CoefficientIndex s 1 (Producer.completedArity G Gamma hmem h)) :
    completedCoefficient G Gamma hmem h c ∈ familyField (KSourceTransport.nativeCoefficient G) := by
  rcases c with ⟨i, x⟩ | ⟨i, u, v⟩
  · change Producer.completedTable G Gamma hmem h i x ∈
      familyField (KSourceTransport.nativeCoefficient G)
    have hb : Producer.completedTable G Gamma hmem h i x ∈
        SingleWeightCompletion.AnswerField.Target (Producer.native G) (Producer.layer G Gamma hmem h) :=
      coefficient_mem_familyField
        (GeneralExtraction.GeneralOriginalTarget.coefficients (Producer.completedTable G Gamma hmem h)) ⟨i, x⟩
    exact native_vertex_le G
      (SingleWeightCompletion.AnswerField.target_le (Producer.native G) (Producer.layer G Gamma hmem h) hb)
  · exact coefficient_mem_familyField (KSourceTransport.nativeCoefficient G) (.inr (i, u, v))

theorem completed_le_native : completedField G Gamma hmem h ≤
    familyField (KSourceTransport.nativeCoefficient G) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨c, rfl⟩
  exact completed_coefficient_mem G Gamma hmem h c

def completedInclusion : completedField G Gamma hmem h →ₐ[ℚ]
    familyField (KSourceTransport.nativeCoefficient G) :=
  IntermediateField.inclusion (completed_le_native G Gamma hmem h)
def completedInclusionComputes : Computes (completedPresentation G Gamma hmem h).encoding
    (KSourceTransport.nativePresentation G).encoding (completedInclusion G Gamma hmem h) :=
  FieldCodec.computes (completedPresentation G Gamma hmem h) (KSourceTransport.nativePresentation G)
    (completedInclusion G Gamma hmem h).toLinearMap

private theorem inclusion_product_of_ambient
    {A B C : IntermediateField ℚ AlgebraicComplex} (hA : A ≤ C) (hB : B ≤ C)
    (x : A) (y : B) (z : C)
    (he : (z : AlgebraicComplex) = (x : AlgebraicComplex) * (y : AlgebraicComplex)) :
    z = IntermediateField.inclusion hA x * IntermediateField.inclusion hB y := by
  apply Subtype.ext
  simpa only [IntermediateField.coe_mul, IntermediateField.coe_inclusion] using he

/-- Actual retained-row query and occurrence scalar restoration for B. This
holds on ALL completed-alphabet inputs, including zero and nullary labels. -/
theorem field_recovery
    (r : ExactSignatureTables.Input s 1 (Producer.completedArity G Gamma hmem h)) :
    completedValue G Gamma hmem h r =
      contextInclusion G Gamma hmem h (RootPreprocessing.context (Producer.completedTable G Gamma hmem h) r) *
      targetInclusion G Gamma hmem h (targetValue G Gamma hmem h
        (RootPreprocessing.query (Producer.completedTable G Gamma hmem h) r)) := by
  apply inclusion_product_of_ambient (context_le_completed G Gamma hmem h)
    (target_le_completed G Gamma hmem h)
  have hs := OriginalFamily.value_exact (Producer.completedTable G Gamma hmem h)
    KSourceTransport.nativeEdges r
  have ht := OriginalFamily.value_exact (Producer.targetTable G Gamma hmem h)
    KSourceTransport.nativeEdges (RootPreprocessing.query (Producer.completedTable G Gamma hmem h) r)
  exact hs.trans ((RootPreprocessing.query_value (Producer.completedTable G Gamma hmem h) r).trans
    (congrArg (fun z : AlgebraicComplex =>
      (RootPreprocessing.context (Producer.completedTable G Gamma hmem h) r : AlgebraicComplex) * z) ht.symm))

end
end Holant.LocalDrafts.Tractability.EOEvaluation.SingleWeightSource.Fields
