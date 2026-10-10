import Holant.Proofs.Algorithms.LocalAffine.Evaluator
import Holant.Proofs.Algorithms.FamilyAnswerTransport
import Holant.Holographic


namespace Holant.LocalDrafts.MainChain.LocalAffineSource
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines ExactSignatureTables
noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (E : Fin b → Kernel AlgebraicComplex) (U : InvertibleKernel)
    (hG : ∀ i, LocalAffine (U.symm.action (G i)))
    (hE : ∀ i, LocalAffine (kernelSignature (Kernel.pullback (E i) U.matrix)))

def transformedFamily : LocalAffineLabels.Family s b arity where
  signatures i := U.symm.action (G i)
  kernels i := Kernel.pullback (E i) U.matrix
  vertexLocal := hG
  edgeLocal := hE

theorem transformed_value (r : Input s b arity) :
    (OriginalFamily.value (transformedFamily G E U hG hE).signatures
      (transformedFamily G E U hG hE).kernels r : AlgebraicComplex)=
      (OriginalFamily.value G E r : AlgebraicComplex) := by
  rw [OriginalFamily.value_exact,OriginalFamily.value_exact]
  have h := congrFun (Network.denote_holographicTransform
    (r.val.realize r.property G E) U.matrix U.inverse U.matrix_inverse) Fin.elim0
  simp only [transformedFamily,InvertibleKernel.action,InvertibleKernel.symm,
    RawClosedNetwork.realize,Network.holographicTransform] at h ⊢
  convert h using 1 <;> rfl

def computes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (OriginalFamily.presentation G E).encoding (OriginalFamily.value G E) := by
  let D := transformedFamily G E U hG hE
  let convert := FamilyAnswerTransport.computes (OriginalFamily.coefficient G E)
    (OriginalFamily.coefficient D.signatures D.kernels)
    (OriginalFamily.coefficient_algebraic G E)
    (OriginalFamily.coefficient_algebraic D.signatures D.kernels)
  apply congrComputes ((LocalAffineEvaluator.computes D).andThen convert)
  intro r
  exact FamilyAnswerTransport.recover_exact (OriginalFamily.coefficient G E)
    (OriginalFamily.coefficient D.signatures D.kernels) (OriginalFamily.value G E r)
    (OriginalFamily.value D.signatures D.kernels r) (transformed_value G E U hG hE r)

include U hG hE in
theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity)
    (OriginalFamily.presentation G E).encoding (OriginalFamily.value G E) :=
  (computes G E U hG hE).inFP

section SourcePredicates
variable (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀ i, (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)

def equalityComputes (h : CommonTransformable localAffineClass Gamma) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.equality)) := by
  let B := Classical.choose h.2
  have hB : IsCommonBasis localAffineClass Gamma B := Classical.choose_spec h.2
  exact computes G (fun _ : Fin 1 => Signature.equality) B
    (fun i => hB.2 _ (hmem i)) (fun _ => hB.1)

def disequalityComputes (h : CommonKPresentationInKCoordinates localAffineClass Gamma) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.disequality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.disequality)) := by
  let B := Classical.choose h.2
  have hB : IsCommonKBasis localAffineClass Gamma B := Classical.choose_spec h.2
  exact computes G (fun _ : Fin 1 => Signature.disequality) B
    (fun i => hB.2 _ (hmem i)) (fun _ => hB.1)

end SourcePredicates
end
end Holant.LocalDrafts.MainChain.LocalAffineSource
