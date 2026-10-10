import Holant.Proofs.Tractability.EOEvaluation.CandidateExecution.Semantics
import Holant.Proofs.Tractability.AffineMachine.FamilySolver


namespace Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Backend
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines ExactSignatureTables FixedGadgetSubstitution
open MainChain
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ} (D : Source.Family s arity)

abbrev sourceCoefficient := OriginalFamily.coefficient D.signatures (Catalogue.kernels : Fin 1 → Kernel AlgebraicComplex)
abbrev sourceAlgebraic := OriginalFamily.coefficient_algebraic D.signatures Catalogue.kernels
abbrev sourcePresentation := OriginalFamily.presentation D.signatures Catalogue.kernels
abbrev sourceValue := OriginalFamily.value D.signatures Catalogue.kernels
abbrev targetCoefficient := OriginalFamily.coefficient (Catalogue.signatures D) Catalogue.kernels
abbrev targetAlgebraic := OriginalFamily.coefficient_algebraic (Catalogue.signatures D) Catalogue.kernels
abbrev targetPresentation := OriginalFamily.presentation (Catalogue.signatures D) Catalogue.kernels
abbrev targetValue := OriginalFamily.value (Catalogue.signatures D) Catalogue.kernels
abbrev commonCoefficient := FamilyFieldInclusion.combined (sourceCoefficient D) (targetCoefficient D)
abbrev commonPresentation := FamilyFieldInclusion.commonPresentation
  (sourceCoefficient D) (targetCoefficient D) (sourceAlgebraic D) (targetAlgebraic D)

def sourceToCommon : Computes (sourcePresentation D).encoding (commonPresentation D).encoding
    (FamilyFieldInclusion.embedding (sourceCoefficient D) (targetCoefficient D)) :=
  FamilyFieldInclusion.embedComputes (sourceCoefficient D) (targetCoefficient D)
    (sourceAlgebraic D) (targetAlgebraic D)
def targetToCommon : Computes (targetPresentation D).encoding (commonPresentation D).encoding
    (FamilyAnswerTransport.targetEmbedding (sourceCoefficient D) (targetCoefficient D)) :=
  FieldCodec.computes (targetPresentation D) (commonPresentation D)
    (FamilyAnswerTransport.targetEmbedding (sourceCoefficient D) (targetCoefficient D)).toLinearMap

/-- Fixed-family branch choice happens before any graph is input. Both cases
instantiate existing physical elimination, coefficient and field machines. -/
def pairedComputes : Computes (Graph.outputEncoding (s := s) (arity := arity))
    (targetPresentation D).encoding (targetValue D) := by
  cases h : Catalogue.branch D with
  | affine =>
    change Computes (RawClosedNetwork.validatedEncoding
      (Catalogue.count (s := s) (arity := arity)) 1 (Catalogue.targetArity (s := s) (arity := arity)))
      (AffineMachine.FamilyField.originalPresentation (Catalogue.affineFamily D h)).encoding
      (AffineMachine.FamilyField.originalValue (Catalogue.affineFamily D h))
    exact AffineMachine.FamilySolver.computes (Catalogue.affineFamily D h)
  | product =>
    change Computes (RawClosedNetwork.validatedEncoding
      (Catalogue.count (s := s) (arity := arity)) 1 (Catalogue.targetArity (s := s) (arity := arity)))
      (ProductMachine.FamilyFieldSolver.originalPresentation (Catalogue.productFamily D h)).encoding
      (ProductMachine.FamilyFieldSolver.originalValue (Catalogue.productFamily D h))
    exact ProductMachine.FamilyFieldSolver.computes (Catalogue.productFamily D h)

theorem tensor_mem (a : Catalogue.Label (s := s) (arity := arity)) (x : Fin (arity a.1.val) → Bool) :
    Catalogue.tensor D a x ∈ familyField (sourceCoefficient D) := by
  rcases a with ⟨i, p⟩
  cases p with
  | none => exact zero_mem _
  | some p =>
    change (if PairLift.Compatible (Catalogue.pairing p) x then D.signatures i x else 0) ∈ _
    split_ifs
    · exact coefficient_mem_familyField (sourceCoefficient D) (.inl ⟨i, x⟩)
    · exact zero_mem _

theorem coefficient_mem (a : CoefficientIndex (Catalogue.count (s := s) (arity := arity)) 1
    (Catalogue.targetArity (s := s) (arity := arity))) :
    targetCoefficient D a ∈ familyField (sourceCoefficient D) := by
  rcases a with ⟨i, x⟩ | ⟨i, x, y⟩
  · change Catalogue.tensor D (Catalogue.codes.symm i)
      (fun j => x (Fin.cast (Catalogue.arity_index i).symm j)) ∈ familyField (sourceCoefficient D)
    exact tensor_mem D (Catalogue.codes.symm i) _
  · exact coefficient_mem_familyField (sourceCoefficient D) (.inr (i, x, y))

theorem target_le_source : familyField (targetCoefficient D) ≤ familyField (sourceCoefficient D) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨a, rfl⟩
  exact coefficient_mem D a

def inclusion : familyField (targetCoefficient D) →ₐ[ℚ] familyField (sourceCoefficient D) :=
  IntermediateField.inclusion (target_le_source D)
def recovered (r : Graph.Output (s := s) (arity := arity)) : familyField (sourceCoefficient D) :=
  FamilyAnswerTransport.recover (sourceCoefficient D) (targetCoefficient D) (targetValue D r)

theorem recovered_inclusion (r : Graph.Output (s := s) (arity := arity)) :
    recovered D r = inclusion D (targetValue D r) :=
  FamilyAnswerTransport.recover_exact (sourceCoefficient D) (targetCoefficient D)
    (inclusion D (targetValue D r)) (targetValue D r)
    (IntermediateField.coe_inclusion (target_le_source D) (targetValue D r)).symm

/-- Actual matrix conversion in the fixed common field, returning precisely
OriginalFamily's original-source coefficient presentation. -/
def computes : Computes (Graph.outputEncoding (s := s) (arity := arity))
    (sourcePresentation D).encoding (recovered D) :=
  congrComputes
    ((pairedComputes D).andThen
      (FamilyAnswerTransport.computes (sourceCoefficient D) (targetCoefficient D)
        (sourceAlgebraic D) (targetAlgebraic D))) (fun _ => rfl)

theorem recovered_ambient (r : Graph.Output (s := s) (arity := arity)) :
    (recovered D r : AlgebraicComplex) =
      (r.val.realize r.property (Catalogue.signatures D) Catalogue.kernels).denote Fin.elim0 := by
  exact (congrArg (fun z : familyField (sourceCoefficient D) => (z : AlgebraicComplex))
      (recovered_inclusion D r)).trans
    ((IntermediateField.coe_inclusion (target_le_source D) (targetValue D r)).trans
      (OriginalFamily.value_exact (Catalogue.signatures D) Catalogue.kernels r))

def responseValue (x : Graph.Input (s := s) (arity := arity)) := recovered D (Graph.value x)
def responseComputes : Computes (Responses.inputEncoding (s := s) (arity := arity))
    (sourcePresentation D).encoding (responseValue D) :=
  congrComputes ((Graph.computes (s := s) (arity := arity)).andThen (computes D)) (fun _ => rfl)

theorem response_ambient (x : Graph.Input (s := s) (arity := arity)) :
    (responseValue D x : AlgebraicComplex) = (Semantics.labelled D x).denote Fin.elim0 :=
  (recovered_ambient D (Graph.value x)).trans (Semantics.realizes D x)

/-- No response-correctness hypothesis: specialize to the defined true list.
There is intentionally no raw-input Computes for constructing that list. -/
theorem true_value (r : Source.Input (s := s) (arity := arity)) :
    responseValue D (r, Responses.truth D r) = sourceValue D r := by
  apply Subtype.ext
  rw [response_ambient, Semantics.true_labelled, CandidatePairing.denote_eq]
  exact (OriginalFamily.value_exact D.signatures Catalogue.kernels r).symm

def checkedComputes : Computes (Responses.inputEncoding (s := s) (arity := arity))
    (pairEncoding encodingBoolBool (sourcePresentation D).encoding)
      (fun x => (Responses.valid x, responseValue D x)) :=
  pairComputes (Responses.validComputes (s := s) (arity := arity)) (responseComputes D)

theorem primitive_bound (x : Graph.Input (s := s) (arity := arity)) :
    primitiveCost (checkedComputes D).machine ((checkedComputes D).outputs x).steps
      (some (Turing.initList (checkedComputes D).machine.computer
        ((Responses.inputEncoding (s := s) (arity := arity)).encode x))) ≤
        (primitivePolynomial (checkedComputes D)).eval
          ((Responses.inputEncoding (s := s) (arity := arity)).encode x).length :=
  computes_primitive_cost (checkedComputes D) x

theorem input_length (x : Graph.Input (s := s) (arity := arity)) :
    ((Responses.inputEncoding (s := s) (arity := arity)).encode x).length =
      2 * ((Source.inputEncoding (s := s) (arity := arity)).encode x.1).length + 4 * x.2.length + 2 := by
  simp [Responses.inputEncoding, pairEncoding_length, LocalAffineMachine.Relabel.WordLookup.word_length]
  omega

def sourcePolynomial : Polynomial ℕ :=
  (primitivePolynomial (checkedComputes D)).comp
    (Polynomial.C (2 + 4 * Source.localBudget s arity) * Polynomial.X + 2)

theorem sized_response_primitive (x : Graph.Input (s := s) (arity := arity))
    (h : x.2.length = (RawColumns.columns x.1).length) :
    primitiveCost (checkedComputes D).machine ((checkedComputes D).outputs x).steps
      (some (Turing.initList (checkedComputes D).machine.computer
        ((Responses.inputEncoding (s := s) (arity := arity)).encode x))) ≤
        (sourcePolynomial D).eval ((Source.inputEncoding (s := s) (arity := arity)).encode x.1).length := by
  have hc := Source.coordinate_bound x.1
  change Fintype.card (Source.Coordinate x.1) ≤ Source.localBudget s arity *
    ((Source.inputEncoding (s := s) (arity := arity)).encode x.1).length at hc
  have hi : ((Responses.inputEncoding (s := s) (arity := arity)).encode x).length ≤
      (2 + 4 * Source.localBudget s arity) *
        ((Source.inputEncoding (s := s) (arity := arity)).encode x.1).length + 2 := by
    rw [input_length, h, RawColumns.length_eq]
    nlinarith
  apply (primitive_bound D x).trans
  simpa [sourcePolynomial] using natPolynomial_eval_mono (primitivePolynomial (checkedComputes D)) hi

end
end Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Backend
