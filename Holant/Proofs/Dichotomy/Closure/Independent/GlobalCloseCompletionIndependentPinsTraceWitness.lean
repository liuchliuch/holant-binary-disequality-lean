import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryTraceOrX
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWTraceCore

/-! The retained trace-or-X witness contains an actual ambient invertible
trace-zero kernel. This supplies the uniform binary input to the ordinary
GHZ terminal without strengthening the source by an assumed gate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTraceWitness
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace U
export GlobalCloseCompletionUnaryTraceOrX (Witness)
end U
namespace T
export GlobalCloseCompletionSymmetricGHZTrace (binary)
end T
namespace B
export Holant.Tractable.SymmetricBinaryPullback (determinant invertibleOfDeterminant)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option Elab.async false

def matrix (a b : AlgebraicComplex) : Kernel AlgebraicComplex:=fun p q=>T.binary a b b ![p,q]
theorem determinant (a b : AlgebraicComplex) : B.determinant (matrix a b)= -a^2-b*b := by
  simp [B.determinant,matrix,T.binary]
  ring

def basis (a b : AlgebraicComplex) (det : -a^2-b*b≠0) : InvertibleKernel:=
  B.invertibleOfDeterminant (matrix a b) (by rw [determinant];exact det)
theorem form (a b : AlgebraicComplex) (det : -a^2-b*b≠0) :
    kernelSignature (basis a b det).matrix=T.binary a b b := by
  funext x
  change T.binary a b b ![x 0,x 1]=T.binary a b b x
  congr 1
  funext i
  fin_cases i <;> rfl
theorem trace (a b : AlgebraicComplex) (det : -a^2-b*b≠0) :
    Matrix.trace (Matrix.of (basis a b det).matrix)=0 := by
  change Matrix.trace (Matrix.of (matrix a b))=0
  simp [Matrix.trace,matrix,T.binary]

theorem exists_kernel {F : SignatureFamily AlgebraicComplex} (resource : U.Witness F) :
    ∃Q : InvertibleKernel,(⟨2,kernelSignature Q.matrix⟩ : AnySignature AlgebraicComplex)∈F ∧
      Matrix.trace (Matrix.of Q.matrix)=0 := by
  cases resource with
  | trace a b member det=>
    exact ⟨basis a b det,by simpa only [form] using member,trace a b det⟩
  | x member=>
    have xform : (xAnchor : Signature AlgebraicComplex 2)=T.binary 0 1 1 := by
      funext x
      cases h0 : x 0 <;> cases h1 : x 1 <;> simp [xAnchor,kernelSignature,Signature.disequality,T.binary,h0,h1]
    have det : -(0:AlgebraicComplex)^2-1*1≠0:=by norm_num
    exact ⟨basis 0 1 det,by simpa only [form,←xform] using member,trace 0 1 det⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTraceWitness
end
