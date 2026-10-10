import Holant.Proofs.Tractability.LocalAffineMachine.Relabel.Semantics
import Holant.Proofs.Algorithms.FamilyAnswerTransport


namespace Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Backend

open Turing Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines ExactSignatureTables FixedGadgetSubstitution
open MainChain
noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ} (D : LocalAffineLabels.Family s b arity)

def sourceCoefficient : CoefficientIndex s b arity → AlgebraicComplex
  | .inl ⟨i, x⟩ => D.signatures i x
  | .inr (i, x, y) => D.kernels i x y

theorem source_algebraic (a : CoefficientIndex s b arity) :
    IsAlgebraic ℚ (sourceCoefficient D a) := Algebra.IsAlgebraic.isAlgebraic _

abbrev targetFamily := Catalogue.family D
abbrev targetCoefficient := AffineMachine.FamilyField.originalCoefficient (targetFamily D)
abbrev target_algebraic := AffineMachine.FamilyField.original_algebraic (targetFamily D)
abbrev targetAll := AffineMachine.FamilyField.combined (targetFamily D)
abbrev targetAll_algebraic := AffineMachine.FamilyField.combined_algebraic (targetFamily D)
abbrev allCoefficient := FamilyFieldInclusion.combined (sourceCoefficient D) (targetAll D)
abbrev all_algebraic := FamilyFieldInclusion.combined_algebraic
  (sourceCoefficient D) (targetAll D) (source_algebraic D) (targetAll_algebraic D)

abbrev sourcePresentation := familyPresentation (sourceCoefficient D) (source_algebraic D)
abbrev targetPresentation := AffineMachine.FamilyField.originalPresentation (targetFamily D)
abbrev targetCommonPresentation := AffineMachine.FamilyField.commonPresentation (targetFamily D)
abbrev commonPresentation := familyPresentation (allCoefficient D) (all_algebraic D)
abbrev sourceEmbedding := FamilyFieldInclusion.embedding (sourceCoefficient D) (targetAll D)
abbrev targetInnerEmbedding := AffineMachine.FamilyField.embedding (targetFamily D)
abbrev targetOuterEmbedding := FamilyAnswerTransport.targetEmbedding (sourceCoefficient D) (targetAll D)

abbrev sourceTables := CommonFieldTables.originalTables (sourceCoefficient D) (source_algebraic D)
abbrev sourceValue := (sourceTables D).evaluate (sourcePresentation D)

theorem sourceValue_exact (r : FixedGadgetSubstitution.Compiler.Input s b arity) :
    (sourceValue D r : AlgebraicComplex) = (LocalAffineLabels.network D r).denote Fin.elim0 := by
  simpa only [sourceValue, sourceTables, sourceCoefficient, LocalAffineLabels.network, id_eq] using
    PresentedScaledFamily.target_value_exact (sourceCoefficient D) (source_algebraic D) id r

def targetValue (x : Graph.Input (s := s) (b := b) (arity := arity)) :=
  AffineMachine.FamilyField.originalValue (targetFamily D) (Graph.value x)

def targetComputes : Computes (Compiler.inputEncoding (s := s) (b := b) (arity := arity))
    (targetPresentation D).encoding (targetValue D) :=
  Compiler.computes.andThen (AffineMachine.FamilySolver.computes (targetFamily D))

theorem targetValue_exact (x : Graph.Input (s := s) (b := b) (arity := arity)) :
    (targetValue D x : AlgebraicComplex) = (Semantics.target D x).denote Fin.elim0 :=
  AffineMachine.FamilyField.originalValue_exact (targetFamily D) (Graph.value x)

def commonValue (x : Graph.Input (s := s) (b := b) (arity := arity)) : familyField (allCoefficient D) :=
  targetOuterEmbedding D (targetInnerEmbedding D (targetValue D x))

def commonComputes : Computes (Compiler.inputEncoding (s := s) (b := b) (arity := arity))
    (commonPresentation D).encoding (commonValue D) :=
  ((targetComputes D).andThen
    (FamilyFieldInclusion.embedComputes (targetCoefficient D)
      (AffineMachine.FamilyField.extra (targetFamily D)) (target_algebraic D)
      (AffineMachine.FamilyField.extra_algebraic (targetFamily D)))).andThen
    (FieldCodec.computes (targetCommonPresentation D) (commonPresentation D)
      (targetOuterEmbedding D).toLinearMap)

theorem commonEmbedding_value (v : familyField (targetCoefficient D)) :
    ((targetOuterEmbedding D (targetInnerEmbedding D v) : familyField (allCoefficient D)) : AlgebraicComplex) = v :=
  (FamilyAnswerTransport.targetEmbedding_value (sourceCoefficient D) (targetAll D) _).trans
    (FamilyFieldInclusion.embedding_value (targetCoefficient D)
      (AffineMachine.FamilyField.extra (targetFamily D)) v)

theorem commonValue_ambient (x : Graph.Input (s := s) (b := b) (arity := arity)) :
    (commonValue D x : AlgebraicComplex) =
      (LocalAffineLabels.labelled D x.1 (Graph.reference x)).denote Fin.elim0 :=
  (commonEmbedding_value D (targetValue D x)).trans
    ((targetValue_exact D x).trans (Semantics.realizes D x))

theorem supported_common (x : Graph.Input (s := s) (b := b) (arity := arity))
    (hx : Semantics.Supported D x) : commonValue D x = sourceEmbedding D (sourceValue D x.1) := by
  apply Subtype.ext
  exact (commonEmbedding_value D (targetValue D x)).trans
    ((targetValue_exact D x).trans ((Semantics.supported_denote D x hx).trans
      ((sourceValue_exact D x.1).symm.trans
        (FamilyFieldInclusion.embedding_value (sourceCoefficient D) (targetAll D) _).symm)))

/-- A total rational retraction, not a claim that arbitrary reference words
preserve the source answer. The supported-value theorem is below. -/
def recoveredValue (x : Graph.Input (s := s) (b := b) (arity := arity)) : familyField (sourceCoefficient D) :=
  (sourceEmbedding D).toLinearMap.leftInverse (commonValue D x)

def computes : Computes (Compiler.inputEncoding (s := s) (b := b) (arity := arity))
    (sourcePresentation D).encoding (recoveredValue D) :=
  (commonComputes D).andThen (FamilyFieldInclusion.recoverComputes
    (sourceCoefficient D) (targetAll D) (source_algebraic D) (targetAll_algebraic D))

theorem supported_value (x : Graph.Input (s := s) (b := b) (arity := arity))
    (hx : Semantics.Supported D x) : recoveredValue D x = sourceValue D x.1 := by
  rw [recoveredValue, supported_common D x hx]
  exact FamilyFieldInclusion.recover_embed (sourceCoefficient D) (targetAll D) (sourceValue D x.1)

theorem supported_ambient (x : Graph.Input (s := s) (b := b) (arity := arity))
    (hx : Semantics.Supported D x) :
    (recoveredValue D x : AlgebraicComplex) = (Semantics.source D x).denote Fin.elim0 := by
  rw [supported_value D x hx, sourceValue_exact]
  rfl

theorem unsupported_common (x : Graph.Input (s := s) (b := b) (arity := arity))
    (hx : ¬ Semantics.Supported D x) : commonValue D x = 0 := by
  apply Subtype.ext
  simpa only [commonValue_ambient, ZeroMemClass.coe_zero] using Semantics.unsupported_labelled_zero D x hx

theorem unsupported_value (x : Graph.Input (s := s) (b := b) (arity := arity))
    (hx : ¬ Semantics.Supported D x) : recoveredValue D x = 0 := by
  simp [recoveredValue, unsupported_common D x hx]

/-- Describes the existing composed machine; no support predicate is evaluated
by a new conditional program. Root owns support search and the final controller. -/
theorem total_value (x : Graph.Input (s := s) (b := b) (arity := arity)) :
    (Semantics.Supported D x ∧ recoveredValue D x = sourceValue D x.1) ∨
      (¬ Semantics.Supported D x ∧ recoveredValue D x = 0) := by
  classical
  by_cases hx : Semantics.Supported D x
  · exact Or.inl ⟨hx, supported_value D x hx⟩
  · exact Or.inr ⟨hx, unsupported_value D x hx⟩

theorem primitive_bound (x : Graph.Input (s := s) (b := b) (arity := arity)) :
    primitiveCost (computes D).machine ((computes D).outputs x).steps
      (some (initList (computes D).machine.computer (Compiler.inputEncoding.encode x))) ≤
        (primitivePolynomial (computes D)).eval (Compiler.inputEncoding.encode x).length :=
  computes_primitive_cost (computes D) x

def outputPolynomial : Polynomial ℕ := (computes D).outputBound.bound

theorem output_bits (x : Graph.Input (s := s) (b := b) (arity := arity)) :
    ((sourcePresentation D).encoding.encode (recoveredValue D x)).length ≤
      (outputPolynomial D).eval (Compiler.inputEncoding.encode x).length :=
  (computes D).outputBound.length_le x

/-- Input representation only; this bound does not assume support or correctness
of a word-producing solver. Short words also satisfy it. -/
theorem short_word_input (x : Graph.Input (s := s) (b := b) (arity := arity))
    (h : x.2.length ≤ 2 * x.1.val.edges.length) :
    (Compiler.inputEncoding.encode x).length ≤ 10 * (RawClosedNetwork.encoding.encode x.1.val).length + 2 := by
  rw [Compiler.input_length]
  have hc := RawClosedNetwork.counts_le_encoded_length x.1.val
  omega

def sourcePrimitivePolynomial : Polynomial ℕ := (primitivePolynomial (computes D)).comp (10 * Polynomial.X + 2)

theorem short_word_primitive (x : Graph.Input (s := s) (b := b) (arity := arity))
    (h : x.2.length ≤ 2 * x.1.val.edges.length) :
    primitiveCost (computes D).machine ((computes D).outputs x).steps
      (some (initList (computes D).machine.computer (Compiler.inputEncoding.encode x))) ≤
        (sourcePrimitivePolynomial D).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  apply (primitive_bound D x).trans
  simpa [sourcePrimitivePolynomial] using natPolynomial_eval_mono
    (primitivePolynomial (computes D)) (short_word_input x h)

end
end Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Backend
