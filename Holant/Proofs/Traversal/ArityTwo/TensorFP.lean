import Holant.Proofs.Traversal.ArityTwo.RawFP
import Holant.Proofs.Traversal.ArityTwo.TensorBytecodeMachine
import Holant.Proofs.Algorithms.CommonFieldTables


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorFP
open Holant Holant.Tractable Holant.Complexity Holant.Algebraic Computability
open BinaryCompose FixedFieldMachines ExactSignatureTables
open FixedGadgetSubstitution TensorTemplates TensorBytecodeMachine
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s b : ℕ} (family : Fin s → AnySignature AlgebraicComplex)
variable (hf : ∀ i, SourceTensorClosure (fun n _ => n = 1 ∨ n = 2) (family i).2)
variable (edges : Fin b → Kernel AlgebraicComplex)

abbrev inputEncoding := TensorCompiler.inputEncoding family hf b
abbrev outputEncoding := (sourcePresentation family hf edges).encoding
abbrev originalTables := PresentedScaledFamily.tables (originalCoefficient family hf edges)
  (original_algebraic family hf edges) id

def answer (r : TensorCompiler.Input family hf b) :=
  (originalTables family hf edges).evaluate (sourcePresentation family hf edges) r

def expandedAnswer (r : TensorCompiler.Input family hf b) :=
  RawFP.answer (presentation family hf edges) (coordinates family hf edges)
    (size family hf) b (arity family hf) (vertexLabels family hf) (edgeLabels family hf)
    (TensorCompiler.value family hf b r)

theorem original_value (r : TensorCompiler.Input family hf b) :
    (answer family hf edges r : AlgebraicComplex) =
      (r.val.realize r.property (originalSignatures family hf b) edges).denote Fin.elim0 := by
  have h := PresentedScaledFamily.target_value_exact (originalCoefficient family hf edges)
    (original_algebraic family hf edges) id r
  simpa [answer,originalTables,originalCoefficient] using h

theorem expanded_value (r : TensorCompiler.Input family hf b) :
    (expandedAnswer family hf edges r : AlgebraicComplex) =
      (r.val.realize r.property (originalSignatures family hf b) edges).denote Fin.elim0 := by
  have he : (expandedAnswer family hf edges r : AlgebraicComplex) =
      ((TensorCompiler.value family hf b r).val.realize (TensorCompiler.value family hf b r).property
        (signatures family hf) edges).denote Fin.elim0 := by
    unfold expandedAnswer RawFP.answer
    change (familyField (combined family hf edges)).subtype _ = _
    rw [← Network.denote_map (familyField (combined family hf edges)).subtype]
    congr 1
    unfold Network.map RawClosedNetwork.realize
    congr 1
    · funext v x
      exact coordinates_exact family hf edges (vertexLabels family hf
        ((TensorCompiler.value family hf b r).val.signatureLabel
          (TensorCompiler.value family hf b r).property v) x)
    · funext e a c
      exact coordinates_exact family hf edges (edgeLabels family hf
        ((TensorCompiler.value family hf b r).val.edgeLabel
          (TensorCompiler.value family hf b r).property e) a c)
  exact he.trans (TensorCompiler.denote family hf b r edges)

def embedding := Holant.LocalDrafts.MainChain.FamilyFieldInclusion.embedding
  (originalCoefficient family hf edges) (coefficient family hf edges)

theorem expanded_embedding (r : TensorCompiler.Input family hf b) :
    expandedAnswer family hf edges r = embedding family hf edges (answer family hf edges r) := by
  apply Subtype.ext
  exact (expanded_value family hf edges r).trans
    ((original_value family hf edges r).symm.trans
      (Holant.LocalDrafts.MainChain.FamilyFieldInclusion.embedding_value
        (originalCoefficient family hf edges) (TensorBytecodeMachine.coefficient family hf edges) _).symm)

/-- No oracle is used: the compiler, matrix evaluator and answer retraction are
one actual finite Boolean-stack machine operating on the original raw input. -/
def computes : Computes (inputEncoding family hf (b := b)) (outputEncoding family hf edges)
    (answer family hf edges) :=
  congrComputes (((TensorCompiler.computes family hf b).andThen
    (RawFP.computes (presentation family hf edges) (coordinates family hf edges) (codec family hf)
      (size family hf) b (arity family hf) (vertexLabels family hf) (edgeLabels family hf)
      (arity_le family hf))).andThen (recover family hf edges)) (by
        intro r
        change (embedding family hf edges).toLinearMap.leftInverse (expandedAnswer family hf edges r) = _
        rw [expanded_embedding]
        exact TensorBytecodeMachine.recover_original family hf edges (answer family hf edges r))

theorem computes_machine : (computes family hf edges).machine = TensorBytecodeMachine.machine family hf edges := by
  simp only [computes,congrComputes,recode,RawFP.computes_machine,
    RunComposition.andThen_machine,TensorBytecodeMachine.machine]

theorem inFP : InFP (inputEncoding family hf (b := b)) (outputEncoding family hf edges) (answer family hf edges) :=
  (computes family hf edges).inFP

/-- The polynomial comes from the real executed machines, including literal
replacement and code generation, and is evaluated on the original raw bits. -/
theorem primitive_bound (r : TensorCompiler.Input family hf b) :
    let w := computes family hf edges
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes family hf edges) r

/-- The derived source codec has exactly the original arities. Its definition
does not narrow the paper's source family to unary/binary input occurrences. -/
theorem original_arity (i : Fin s) : originalArity family hf b i.val = (family i).1 :=
  originalArity_fin family hf b i

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorFP
