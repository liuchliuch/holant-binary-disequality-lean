import Holant.Proofs.Traversal.ArityTwo.TensorCompiler
import Holant.Proofs.Traversal.ArityTwo.RawBytecodeMachine
import Holant.Proofs.Algorithms.FamilyFieldInclusion


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorBytecodeMachine
open Holant Holant.Tractable Holant.Complexity Holant.Algebraic Computability
open BinaryCompose FixedFieldMachines ExactSignatureTables
open Holant.OneHot.StackProgram.GraphLabelEncoding
open TensorTemplates
noncomputable section

variable {s b : ℕ} (family : Fin s → AnySignature AlgebraicComplex)
variable (hf : ∀ i, SourceTensorClosure (fun n _ => n = 1 ∨ n = 2) (family i).2)
variable (edges : Fin b → Kernel AlgebraicComplex)

abbrev OriginalLiteral := CoefficientIndex s b (originalArity family hf b)
abbrev Literal := CoefficientIndex (size family hf) b (arity family hf)

def originalCoefficient : OriginalLiteral family hf (b := b) → AlgebraicComplex
  | .inl ⟨i,x⟩ => originalSignatures family hf b i x
  | .inr (i,a,b) => edges i a b

def coefficient : Literal family hf (b := b) → AlgebraicComplex
  | .inl ⟨i,x⟩ => signatures family hf i x
  | .inr (i,a,b) => edges i a b

theorem original_algebraic (a : OriginalLiteral family hf (b := b)) :
    IsAlgebraic ℚ (originalCoefficient family hf edges a) := Algebra.IsAlgebraic.isAlgebraic _

theorem coefficient_algebraic (a : Literal family hf (b := b)) :
    IsAlgebraic ℚ (coefficient family hf edges a) := Algebra.IsAlgebraic.isAlgebraic _

abbrev combined := Holant.LocalDrafts.MainChain.FamilyFieldInclusion.combined
  (originalCoefficient family hf edges) (coefficient family hf edges)

theorem combined_algebraic (a : OriginalLiteral family hf (b := b) ⊕ Literal family hf (b := b)) :
    IsAlgebraic ℚ (combined family hf edges a) := Algebra.IsAlgebraic.isAlgebraic _

abbrev presentation := familyPresentation (combined family hf edges) (combined_algebraic family hf edges)
abbrev sourcePresentation := familyPresentation (originalCoefficient family hf edges) (original_algebraic family hf edges)

def coordinates (a : Literal family hf (b := b)) :
    Fin (Module.finrank ℚ (familyField (combined family hf edges))) → ℚ :=
  familyCoordinates (combined family hf edges) (combined_algebraic family hf edges) (.inr a)

theorem coordinates_exact (a : Literal family hf (b := b)) :
    ((presentation family hf edges).decode (coordinates family hf edges a) : AlgebraicComplex) =
      coefficient family hf edges a :=
  familyCoordinates_spec (combined family hf edges) (combined_algebraic family hf edges) (.inr a)

def vertexLabels (i : Fin (size family hf)) (x : Fin (arity family hf i.val) → Bool) : Literal family hf (b := b) :=
  .inl ⟨i,x⟩
def edgeLabels (i : Fin b) (a c : Bool) : Literal family hf (b := b) := .inr (i,a,c)
def codec : Encoding (Literal family hf (b := b)) Bool := coefficientEncoding (size family hf) b (arity family hf)

def recover := Holant.LocalDrafts.MainChain.FamilyFieldInclusion.recoverComputes
  (originalCoefficient family hf edges) (coefficient family hf edges)
  (original_algebraic family hf edges) (coefficient_algebraic family hf edges)

/-- All introduced factor entries, zeros, units and scale literals live in one
fixed coefficient field. The final real retraction returns the old codec. -/
def machine : Machine :=
  ((TensorCompiler.computes family hf b).machine.compose
    (RawBytecodeMachine.machine (size family hf) b (arity family hf)
      (vertexLabels family hf) (edgeLabels family hf) (codec family hf)
      (presentation family hf edges) (coordinates family hf edges))).compose
    (recover family hf edges).machine

theorem recover_original (z : familyField (originalCoefficient family hf edges)) :
    (Holant.LocalDrafts.MainChain.FamilyFieldInclusion.embedding
      (originalCoefficient family hf edges) (coefficient family hf edges)).toLinearMap.leftInverse
      (Holant.LocalDrafts.MainChain.FamilyFieldInclusion.embedding
        (originalCoefficient family hf edges) (coefficient family hf edges) z) = z :=
  Holant.LocalDrafts.MainChain.FamilyFieldInclusion.recover_embed
    (originalCoefficient family hf edges) (coefficient family hf edges) z

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorBytecodeMachine
