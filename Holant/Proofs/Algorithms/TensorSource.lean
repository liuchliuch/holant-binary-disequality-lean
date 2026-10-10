import Holant.Proofs.Traversal.ArityTwo.TensorFP
import Holant.Proofs.Algorithms.OriginalFamily
import Holant.Proofs.Algorithms.RawArityTransport
import Holant.Proofs.Algorithms.FamilyAnswerTransport


namespace Holant.LocalDrafts.MainChain.TensorSource
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines ExactSignatureTables
open Holant.LocalDrafts.TraversalCompletion.ArityTwo
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (hG : ∀ i, SourceTensorClosure (fun n _ => n=1 ∨ n=2) (G i))

def family : Fin s → AnySignature AlgebraicComplex := fun i => ⟨arity i.val,G i⟩

def arityAgree (b : ℕ) (i : Fin s) :
    arity i.val=TensorTemplates.originalArity (family G) hG b i.val :=
  (TensorTemplates.originalArity_fin (family G) hG b i).symm

theorem signatures_eq (b : ℕ) :
    RawArityTransport.signatures (arityAgree G hG b) G=
      TensorTemplates.originalSignatures (family G) hG b := by
  funext i x
  rfl

variable {b : ℕ} (E : Fin b → Kernel AlgebraicComplex)

def input (_E : Fin b → Kernel AlgebraicComplex) (r : ExactSignatureTables.Input s b arity) :
    TensorCompiler.Input (family G) hG b :=
  RawArityTransport.input (arityAgree G hG b) r

theorem target_value (r : ExactSignatureTables.Input s b arity) :
    (TensorFP.answer (family G) hG E (input G hG E r) : AlgebraicComplex)=
      (OriginalFamily.value G E r : AlgebraicComplex) := by
  apply (TensorFP.original_value (family G) hG E (input G hG E r)).trans
  apply Eq.trans _ (OriginalFamily.value_exact G E r).symm
  rw [← signatures_eq G hG b]
  exact RawArityTransport.denote (arityAgree G hG b) G E r

/-- The first machine preserves the original bytes; the last machine is the
fixed rational answer conversion. Neither costs a semantic oracle call. -/
def computes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (OriginalFamily.presentation G E).encoding (OriginalFamily.value G E) := by
  let front := RawArityTransport.computes (b := b) (arityAgree G hG b)
  let solve := TensorFP.computes (family G) hG E
  let convert := FamilyAnswerTransport.computes (OriginalFamily.coefficient G E)
    (TensorBytecodeMachine.originalCoefficient (family G) hG E)
    (OriginalFamily.coefficient_algebraic G E)
    (TensorBytecodeMachine.original_algebraic (family G) hG E)
  apply congrComputes ((front.andThen solve).andThen convert)
  intro r
  exact FamilyAnswerTransport.recover_exact (OriginalFamily.coefficient G E)
    (TensorBytecodeMachine.originalCoefficient (family G) hG E)
    (OriginalFamily.value G E r) (TensorFP.answer (family G) hG E (input G hG E r))
    (target_value G hG E r)

include hG in
theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity)
    (OriginalFamily.presentation G E).encoding (OriginalFamily.value G E) :=
  (computes G hG E).inFP

theorem primitive_bound (r : ExactSignatureTables.Input s b arity) :
    primitiveCost (computes G hG E).machine ((computes G hG E).outputs r).steps
      (some (Turing.initList (computes G hG E).machine.computer
        ((RawClosedNetwork.validatedEncoding s b arity).encode r))) ≤
      (primitivePolynomial (computes G hG E)).eval
        ((RawClosedNetwork.validatedEncoding s b arity).encode r).length :=
  computes_primitive_cost (computes G hG E) r

end
end Holant.LocalDrafts.MainChain.TensorSource
