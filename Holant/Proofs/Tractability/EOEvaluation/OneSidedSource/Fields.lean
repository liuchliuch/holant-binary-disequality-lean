import Holant.Proofs.Tractability.EOEvaluation.OneSidedSource.Producer
import Holant.Complexity.FixedFieldMachines.Concrete


namespace Holant.LocalDrafts.Tractability.EOEvaluation.OneSidedSource.Fields
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines ExactSignatureTables
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

abbrev centralCoefficient := OriginalFamily.coefficient (Producer.central G) KSourceTransport.nativeEdges
abbrev centralField := familyField (centralCoefficient G)
abbrev centralPresentation := OriginalFamily.presentation (Producer.central G) KSourceTransport.nativeEdges
abbrev centralValue := OriginalFamily.value (Producer.central G) KSourceTransport.nativeEdges
abbrev targetCoefficient := OriginalFamily.coefficient (Producer.targetTable G) KSourceTransport.nativeEdges
abbrev targetField := familyField (targetCoefficient G)
abbrev targetPresentation := OriginalFamily.presentation (Producer.targetTable G) KSourceTransport.nativeEdges
abbrev targetValue := OriginalFamily.value (Producer.targetTable G) KSourceTransport.nativeEdges

theorem target_coefficient_mem
    (a : CoefficientIndex (Producer.count G) 1 (Producer.targetArity G)) :
    targetCoefficient G a ∈ centralField G := by
  rcases a with ⟨j, x⟩ | ⟨j, u, v⟩
  · change RootPreprocessing.targetTable (Producer.central G) j x ∈ centralField G
    rw [RootPreprocessing.target_entry (Producer.central G) j x]
    exact coefficient_mem_familyField (centralCoefficient G)
      (.inl ⟨RootPreprocessing.includeLabel (Producer.central G) j,
        fun k => x (Fin.cast (RootPreprocessing.target_arity (Producer.central G) j).symm k)⟩)
  · exact coefficient_mem_familyField (centralCoefficient G) (.inr (j, u, v))

theorem target_le_central : targetField G ≤ centralField G := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨a, rfl⟩
  exact target_coefficient_mem G a

def targetInclusion : targetField G →ₐ[ℚ] centralField G :=
  IntermediateField.inclusion (target_le_central G)
def targetInclusionComputes : Computes (targetPresentation G).encoding
    (centralPresentation G).encoding (targetInclusion G) :=
  FieldCodec.computes (targetPresentation G) (centralPresentation G)
    (targetInclusion G).toLinearMap

theorem central_coefficient_mem (a : CoefficientIndex s 1 arity) :
    centralCoefficient G a ∈ familyField (KSourceTransport.nativeCoefficient G) := by
  rcases a with ⟨i, x⟩ | ⟨i, u, v⟩
  · change Producer.central G i x ∈ familyField (KSourceTransport.nativeCoefficient G)
    by_cases hx : 2 * Holant.weight x = arity i.val
    · have hm := coefficient_mem_familyField (KSourceTransport.nativeCoefficient G) (.inl ⟨i, x⟩)
      change KSourceTransport.nativeSignatures G i x ∈
        familyField (KSourceTransport.nativeCoefficient G) at hm
      simpa only [Producer.central, Signature.centralRestriction, if_pos hx, Producer.native] using hm
    · simp only [Producer.central, Signature.centralRestriction, if_neg hx]
      exact zero_mem _
  · exact coefficient_mem_familyField (KSourceTransport.nativeCoefficient G) (.inr (i, u, v))

theorem central_le_native : centralField G ≤ familyField (KSourceTransport.nativeCoefficient G) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨a, rfl⟩
  exact central_coefficient_mem G a

def centralInclusion : centralField G →ₐ[ℚ] familyField (KSourceTransport.nativeCoefficient G) :=
  IntermediateField.inclusion (central_le_native G)
def centralInclusionComputes : Computes (centralPresentation G).encoding
    (KSourceTransport.nativePresentation G).encoding (centralInclusion G) :=
  FieldCodec.computes (centralPresentation G) (KSourceTransport.nativePresentation G)
    (centralInclusion G).toLinearMap

/-- Keep an inclusion equality abstract in its two fields. Instantiating this
small proof does not normalize a whole chosen presentation or graph value. -/
private theorem inclusion_eq_of_ambient {E F : IntermediateField ℚ AlgebraicComplex}
    (hEF : E ≤ F) (x : E) (y : F) (hxy : (x : AlgebraicComplex) = (y : AlgebraicComplex)) :
    IntermediateField.inclusion hEF x = y :=
  Subtype.ext ((IntermediateField.coe_inclusion hEF x).trans hxy)

private theorem context_coefficient_eq (a : CoefficientIndex s 1 arity) :
    RootPreprocessing.sourceCoefficient (Producer.central G) a = centralCoefficient G a := by
  rcases a with ⟨i,x⟩ | ⟨i,u,v⟩ <;> rfl

/-- The preprocessing occurrence scalar uses its prescribed C+X field. Its
coefficients are proved to lie in the central answer field; codecs are not
identified by this containment proof. -/
theorem context_le_central : RootPreprocessing.sourceField (Producer.central G) ≤ centralField G := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨a,rfl⟩
  rw [context_coefficient_eq G a]
  exact coefficient_mem_familyField (centralCoefficient G) a

def contextInclusion : RootPreprocessing.sourceField (Producer.central G) →ₐ[ℚ] centralField G :=
  IntermediateField.inclusion (context_le_central G)

/-- Restore EACH nullary occurrence. A zero occurrence selects a valid empty
query and context zero; empty graphs have context one. No identity label is
required and no potentially dangling positive-arity row is deleted on the
zero branch. The targetValue is in the actual Q+X presentation. -/
theorem field_recovery (r : Producer.Input (s := s) (arity := arity)) :
    centralValue G r = contextInclusion G (RootPreprocessing.context (Producer.central G) r) *
      targetInclusion G (targetValue G (RootPreprocessing.query (Producer.central G) r)) := by
  apply Subtype.ext
  have hcontext := IntermediateField.coe_inclusion (context_le_central G)
    (RootPreprocessing.context (Producer.central G) r)
  have htarget := IntermediateField.coe_inclusion (target_le_central G)
    (targetValue G (RootPreprocessing.query (Producer.central G) r))
  have hm := (centralField G).coe_mul
    (contextInclusion G (RootPreprocessing.context (Producer.central G) r))
    (targetInclusion G (targetValue G (RootPreprocessing.query (Producer.central G) r)))
  have hproduct := congrArg₂ (fun x y : AlgebraicComplex => x*y)
    hcontext.symm
    ((OriginalFamily.value_exact (Producer.targetTable G) KSourceTransport.nativeEdges
      (RootPreprocessing.query (Producer.central G) r)).symm.trans htarget.symm)
  exact (OriginalFamily.value_exact (Producer.central G) KSourceTransport.nativeEdges r).trans
    (((RootPreprocessing.query_value (Producer.central G) r).trans hproduct).trans hm.symm)

variable (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀ i, (⟨arity i.val, G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)

include hmem in
theorem native_recovery (h : OneSidedAlternative (preprocess Gamma))
    (r : Producer.Input (s := s) (arity := arity)) :
    centralInclusion G (centralValue G r) = KSourceTransport.nativeValue G r := by
  exact inclusion_eq_of_ambient (central_le_native G) (centralValue G r)
    (KSourceTransport.nativeValue G r) (Producer.central_value_exact G Gamma hmem h r)

end
end Holant.LocalDrafts.Tractability.EOEvaluation.OneSidedSource.Fields
