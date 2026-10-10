import Holant.Proofs.Tractability.AffineMachine.FamilySolver
import Holant.Proofs.Algorithms.FamilyAnswerTransport
import Holant.Proofs.Algorithms.OriginalFamily
import Holant.Holographic


namespace Holant.LocalDrafts.MainChain.AffineSource
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines ExactSignatureTables FixedGadgetSubstitution
open Holant.LocalDrafts.Tractability.AffineMachine
noncomputable section

variable {s b : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (E : Fin b → Kernel AlgebraicComplex)

abbrev coefficient := OriginalFamily.coefficient G E
abbrev coefficient_algebraic := OriginalFamily.coefficient_algebraic G E
abbrev presentation := OriginalFamily.presentation G E
abbrev tables := OriginalFamily.tables G E
abbrev value := OriginalFamily.value G E

theorem value_exact (r : ExactSignatureTables.Input s b arity) :
    (value G E r : AlgebraicComplex)=(r.val.realize r.property G E).denote Fin.elim0 :=
  OriginalFamily.value_exact G E r

variable (U : InvertibleKernel)
    (hG : ∀ i, Affine (U.symm.action (G i)))
    (hE : ∀ i, Affine (kernelSignature (Kernel.pullback (E i) U.matrix)))

def transformedFamily : Assembly.Family s b arity where
  signatures i := U.symm.action (G i)
  kernels i := Kernel.pullback (E i) U.matrix
  vertexAffine := hG
  edgeAffine := hE

theorem transformed_value (r : ExactSignatureTables.Input s b arity) :
    (FamilyField.originalValue (transformedFamily G E U hG hE) r : AlgebraicComplex)=
      (value G E r : AlgebraicComplex) := by
  rw [FamilyField.originalValue_exact,value_exact]
  have h := congrFun (Network.denote_holographicTransform
    (r.val.realize r.property G E) U.matrix U.inverse U.matrix_inverse) Fin.elim0
  simp only [transformedFamily,InvertibleKernel.action,InvertibleKernel.symm,
    RawClosedNetwork.realize,Network.holographicTransform] at h ⊢
  convert h using 1 <;> rfl

def computes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (presentation G E).encoding (value G E) := by
  let D := transformedFamily G E U hG hE
  let convert := FamilyAnswerTransport.computes (coefficient G E)
    (FamilyField.originalCoefficient D) (coefficient_algebraic G E) (FamilyField.original_algebraic D)
  apply congrComputes ((FamilySolver.computes D).andThen convert)
  intro r
  exact FamilyAnswerTransport.recover_exact (coefficient G E)
    (FamilyField.originalCoefficient D) (value G E r) (FamilyField.originalValue D r)
    (transformed_value G E U hG hE r)

include U hG hE in
theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity)
    (presentation G E).encoding (value G E) := (computes G E U hG hE).inFP

theorem primitive_bound (r : ExactSignatureTables.Input s b arity) :
    primitiveCost (computes G E U hG hE).machine ((computes G E U hG hE).outputs r).steps
      (some (Turing.initList (computes G E U hG hE).machine.computer
        ((RawClosedNetwork.validatedEncoding s b arity).encode r))) ≤
      (primitivePolynomial (computes G E U hG hE)).eval
        ((RawClosedNetwork.validatedEncoding s b arity).encode r).length :=
  computes_primitive_cost (computes G E U hG hE) r

section SourcePredicates
variable (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀ i, (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)

/-- The basis is chosen once from the fixed family's actual source predicate.
No graph input carries a basis, support system or complexity certificate. -/
def equalityComputes (h : CommonTransformable affineClass Gamma) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (value G (fun _ : Fin 1 => Signature.equality)) := by
  let B := Classical.choose h.2
  have hB : IsCommonBasis affineClass Gamma B := Classical.choose_spec h.2
  exact computes G (fun _ : Fin 1 => Signature.equality) B
    (fun i => hB.2 _ (hmem i)) (fun _ => hB.1)

def disequalityComputes (h : CommonKPresentationInKCoordinates affineClass Gamma) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (presentation G (fun _ : Fin 1 => Signature.disequality)).encoding
      (value G (fun _ : Fin 1 => Signature.disequality)) := by
  let B := Classical.choose h.2
  have hB : IsCommonKBasis affineClass Gamma B := Classical.choose_spec h.2
  exact computes G (fun _ : Fin 1 => Signature.disequality) B
    (fun i => hB.2 _ (hmem i)) (fun _ => hB.1)

include hmem in
theorem equality_inFP (h : CommonTransformable affineClass Gamma) :
    InFP (RawClosedNetwork.validatedEncoding s 1 arity)
      (presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (value G (fun _ : Fin 1 => Signature.equality)) :=
  (equalityComputes G Gamma hmem h).inFP

include hmem in
theorem disequality_inFP (h : CommonKPresentationInKCoordinates affineClass Gamma) :
    InFP (RawClosedNetwork.validatedEncoding s 1 arity)
      (presentation G (fun _ : Fin 1 => Signature.disequality)).encoding
      (value G (fun _ : Fin 1 => Signature.disequality)) :=
  (disequalityComputes G Gamma hmem h).inFP
end SourcePredicates

end
end Holant.LocalDrafts.MainChain.AffineSource
