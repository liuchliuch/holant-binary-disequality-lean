import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZFrame

/-! The square of the original cap supplies the Gram row in the normalized
source. Combining this with a transformed trace-zero row gives its actual
similarity transform, which remains nonsingular and trace-zero. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZGram
open Holant Holant.Tractable
namespace T
export GlobalCloseCompletionEq4CommonBasis (transpose edge edge_matrix)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false

def scale (c : AlgebraicComplex) (E : Kernel AlgebraicComplex) : Kernel AlgebraicComplex:=fun p q=>c*E p q
theorem scale_mul (c : AlgebraicComplex) (A B : Kernel AlgebraicComplex) :
    Kernel.mul (scale c A) B=scale c (Kernel.mul A B) := by
  funext p q
  simp [scale,Kernel.mul_apply]
  ring
theorem mul_scale (c : AlgebraicComplex) (A B : Kernel AlgebraicComplex) :
    Kernel.mul A (scale c B)=scale c (Kernel.mul A B) := by
  funext p q
  simp [scale,Kernel.mul_apply]
  ring
theorem scale_scale (c d : AlgebraicComplex) (A : Kernel AlgebraicComplex) :
    scale c (scale d A)=scale (c*d) A := by funext p q; simp [scale,mul_assoc]

def inverseGram (R : InvertibleKernel) : InvertibleKernel := (T.transpose R.symm).comp R.symm

theorem edge_unique (R : InvertibleKernel) (J : Kernel AlgebraicComplex)
    (normalized : Kernel.pullback J R.matrix=Signature.equality) : J=(inverseGram R).matrix := by
  have cancel : Kernel.mul (Kernel.transpose R.inverse) (Kernel.transpose R.matrix)=Signature.equality := by
    rw [←Kernel.transpose_mul,R.matrix_inverse,Kernel.transpose_equality]
  have h:=congrArg (fun E=>Kernel.mul (Kernel.mul (Kernel.transpose R.inverse) E) R.inverse) normalized
  simp only [Kernel.pullback,Kernel.mul_assoc] at h
  rw [←Kernel.mul_assoc (Kernel.transpose R.inverse) (Kernel.transpose R.matrix),cancel,Kernel.equality_mul,
    R.matrix_inverse,Kernel.mul_equality,Kernel.equality_mul] at h
  exact h

theorem cap_form (R : InvertibleKernel) (B J : Kernel AlgebraicComplex) (c : AlgebraicComplex)
    (normalized : Kernel.pullback J R.matrix=Signature.equality)
    (inverse : Kernel.mul B J=scale c Signature.equality) :
    B=scale c (Kernel.mul R.matrix (Kernel.transpose R.matrix)) := by
  have h:=GlobalCloseCompletionSymmetricGHZFrame.scalar_inverse (inverseGram R) B c
    (by rw [←edge_unique R J normalized];exact inverse)
  exact h

theorem square_gram (R : InvertibleKernel) (B J : Kernel AlgebraicComplex) (c : AlgebraicComplex)
    (normalized : Kernel.pullback J R.matrix=Signature.equality)
    (inverse : Kernel.mul B J=scale c Signature.equality) :
    R.symm.action (kernelSignature (Kernel.mul B B))=
      kernelSignature (scale (c^2) (Kernel.pullback Signature.equality R.matrix)) := by
  change Signature.coordinateAction (fun _ : Fin 2=>R.inverse) (kernelSignature (Kernel.mul B B))=_
  rw [coordinateAction_kernelSignature,cap_form R B J c normalized inverse]
  simp only [scale_mul,mul_scale,scale_scale]
  apply congrArg kernelSignature
  rw [show c*c=c^2 by ring]
  apply congrArg (scale (c^2))
  have cancel : Kernel.mul (Kernel.transpose R.matrix) (Kernel.transpose R.inverse)=Signature.equality := by
    rw [←Kernel.transpose_mul,R.inverse_matrix,Kernel.transpose_equality]
  simp only [Kernel.pullback,Kernel.mul_assoc,Kernel.equality_mul]
  rw [←Kernel.mul_assoc R.inverse R.matrix,R.inverse_matrix,Kernel.equality_mul,cancel,Kernel.mul_equality]

def transformedRow (R Q : InvertibleKernel) : InvertibleKernel :=
  (R.symm.comp Q).comp (T.transpose R.symm)
def similarity (R Q : InvertibleKernel) : InvertibleKernel := (R.symm.comp Q).comp R

theorem row_action (R Q : InvertibleKernel) :
    R.symm.action (kernelSignature Q.matrix)=kernelSignature (transformedRow R Q).matrix :=
  coordinateAction_kernelSignature R.inverse Q.matrix

theorem gram_product (R Q : InvertibleKernel) :
    Kernel.mul (transformedRow R Q).matrix (Kernel.pullback Signature.equality R.matrix)=
      (similarity R Q).matrix := by
  have cancel : Kernel.mul (Kernel.transpose R.inverse) (Kernel.transpose R.matrix)=Signature.equality := by
    rw [←Kernel.transpose_mul,R.matrix_inverse,Kernel.transpose_equality]
  simp only [transformedRow,similarity,InvertibleKernel.comp,InvertibleKernel.symm,T.transpose,
    Kernel.pullback,Kernel.mul_assoc,Kernel.equality_mul]
  rw [←Kernel.mul_assoc (Kernel.transpose R.inverse) (Kernel.transpose R.matrix),cancel,Kernel.equality_mul]

theorem similarity_trace (R Q : InvertibleKernel) :
    Matrix.trace (similarity R Q).matrix=Matrix.trace Q.matrix := by
  have h:=congrArg (fun E : Kernel AlgebraicComplex=>Q.matrix false false*E false false+
    Q.matrix false true*E true false+Q.matrix true false*E false true+Q.matrix true true*E true true) R.matrix_inverse
  simp only [Kernel.mul_apply,Signature.equality,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq_false,
    mul_one,mul_zero,add_zero] at h
  simp [similarity,InvertibleKernel.comp,InvertibleKernel.symm,Matrix.trace,Kernel.mul_apply]
  linear_combination h

theorem similarity_determinant (R Q : InvertibleKernel) :
    SymmetricBinaryPullback.determinant (similarity R Q).matrix≠0 :=
  SymmetricBinaryPullback.determinant_ne_zero (similarity R Q)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZGram
end
