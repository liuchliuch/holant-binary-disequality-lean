import Holant.Proofs.Tractability.ProductMachine.FamilyFieldSolver


namespace Holant.LocalDrafts.Tractability.ProductMachine.CommonBasisSolver

open Computability Holant.Tractable Holant.Complexity Holant.Algebraic
open BinaryCompose FixedFieldMachines ProductElimination
open ExactSignatureTables Holant.Complexity.FixedGadgetSubstitution
noncomputable section

variable {s b : ℕ} {arity : ℕ → ℕ} (C : CommonProductData s b arity)

def sourceCoefficient : CoefficientIndex s b arity → AlgebraicComplex
  | .inl ⟨i, x⟩ => C.signatures i x
  | .inr (i, x, y) => C.kernels i x y

theorem source_algebraic (a : CoefficientIndex s b arity) :
    IsAlgebraic ℚ (sourceCoefficient C a) := Algebra.IsAlgebraic.isAlgebraic _

abbrev transformedCoefficient := FamilyFieldSolver.combined C.transformed
abbrev transformed_algebraic := FamilyFieldSolver.combined_algebraic C.transformed

abbrev allCoefficient := Holant.LocalDrafts.MainChain.FamilyFieldInclusion.combined
  (sourceCoefficient C) (transformedCoefficient C)

theorem all_algebraic
    (a : CoefficientIndex s b arity ⊕ (CoefficientIndex s b arity ⊕ FamilyCatalogue.Slot C.transformed)) :
    IsAlgebraic ℚ (allCoefficient C a) :=
  Holant.LocalDrafts.MainChain.FamilyFieldInclusion.combined_algebraic
    (sourceCoefficient C) (transformedCoefficient C) (source_algebraic C) (transformed_algebraic C) a

abbrev sourcePresentation := familyPresentation (sourceCoefficient C) (source_algebraic C)
abbrev transformedPresentation := FamilyFieldSolver.commonPresentation C.transformed
abbrev commonPresentation := familyPresentation (allCoefficient C) (all_algebraic C)
abbrev sourceEmbedding := Holant.LocalDrafts.MainChain.FamilyFieldInclusion.embedding
  (sourceCoefficient C) (transformedCoefficient C)

theorem transformed_le : familyField (transformedCoefficient C) ≤ familyField (allCoefficient C) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x ⟨a, rfl⟩
  exact coefficient_mem_familyField (allCoefficient C) (.inr a)

def transformedEmbedding : familyField (transformedCoefficient C) →ₐ[ℚ] familyField (allCoefficient C) :=
  IntermediateField.inclusion (transformed_le C)

@[simp] theorem transformedEmbedding_value (x : familyField (transformedCoefficient C)) :
    ((transformedEmbedding C x : familyField (allCoefficient C)) : AlgebraicComplex) = x :=
  IntermediateField.coe_inclusion (transformed_le C) x

abbrev sourceTables := Holant.LocalDrafts.MainChain.CommonFieldTables.originalTables
  (sourceCoefficient C) (source_algebraic C)
abbrev sourceValue := (sourceTables C).evaluate (sourcePresentation C)

def commonValue (r : Input s b arity) : familyField (allCoefficient C) :=
  transformedEmbedding C (FamilyFieldSolver.commonValue C.transformed r)

theorem sourceValue_exact (r : Input s b arity) :
    (sourceValue C r : AlgebraicComplex) = (C.original r).denote Fin.elim0 := by
  simpa only [sourceValue, sourceTables, sourceCoefficient, CommonProductData.original, sourcePresentation,
    Holant.LocalDrafts.MainChain.CommonFieldTables.originalTables, id_eq] using
    PresentedScaledFamily.target_value_exact (sourceCoefficient C) (source_algebraic C) id r

/-- No equality of the two coefficient fields is presumed. The result is in
the embedded original field because both network values agree in the ambient
algebraic-complex field, and that field's subtype map is injective. -/
theorem commonValue_sourceEmbedding (r : Input s b arity) :
    commonValue C r = sourceEmbedding C (sourceValue C r) := by
  apply Subtype.ext
  calc
    (commonValue C r : AlgebraicComplex) = (FamilyFieldSolver.commonValue C.transformed r : AlgebraicComplex) :=
      transformedEmbedding_value C _
    _ = C.transformed.evaluate r := FamilyFieldSolver.commonValue_ambient C.transformed r
    _ = (C.original r).denote Fin.elim0 := C.evaluate_original r
    _ = (sourceValue C r : AlgebraicComplex) := (sourceValue_exact C r).symm
    _ = ((sourceEmbedding C (sourceValue C r) : familyField (allCoefficient C)) : AlgebraicComplex) :=
      (Holant.LocalDrafts.MainChain.FamilyFieldInclusion.embedding_value _ _ _).symm

/-- Both the transformed evaluator and the fixed basis conversion are actual
finite Boolean-stack programs; no graph query or free output map is assumed. -/
def commonComputes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (commonPresentation C).encoding (commonValue C) :=
  (FamilyFieldSolver.commonComputes C.transformed).andThen
    (Holant.LocalDrafts.MainChain.FieldCodec.computes
      (transformedPresentation C) (commonPresentation C) (transformedEmbedding C).toLinearMap)

def computes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (sourcePresentation C).encoding (sourceValue C) :=
  congrComputes ((commonComputes C).andThen
    (Holant.LocalDrafts.MainChain.FamilyFieldInclusion.recoverComputes
      (sourceCoefficient C) (transformedCoefficient C) (source_algebraic C) (transformed_algebraic C)))
    (fun r => by
      dsimp only [Function.comp_def]
      rw [commonValue_sourceEmbedding]
      exact Holant.LocalDrafts.MainChain.FamilyFieldInclusion.recover_embed
        (sourceCoefficient C) (transformedCoefficient C) (sourceValue C r))

theorem primitive_bound (r : Input s b arity) :
    let w := computes C
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
      (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes C) r

def answerBits (r : Input s b arity) := (sourcePresentation C).encoding.encode (sourceValue C r)

theorem answerBits_decode (r : Input s b arity) :
    (sourcePresentation C).encoding.decode (answerBits C r) = some (sourceValue C r) :=
  (sourcePresentation C).encoding.decode_encode _

end
end Holant.LocalDrafts.Tractability.ProductMachine.CommonBasisSolver
