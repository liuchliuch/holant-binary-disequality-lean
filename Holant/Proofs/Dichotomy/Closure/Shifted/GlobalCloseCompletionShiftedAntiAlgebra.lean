import Holant.EightVertex.ProductAnchor.Source
import Holant.Marked.Fusion

/-! Exact full weighted-anti table under the explicit parity equality basis.
The scalar and the two unequal phase weights are preserved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedAntiAlgebra
open Holant Holant.Tractable Holant.Marked
open Holant.EightVertex.ProductAnchor

theorem normalization_from_sector (z u : AlgebraicComplex) (hz : z≠0) (hu : u≠0)
    (square : u^2=2) (B : Kernel AlgebraicComplex) :
    Kernel.mul (Kernel.mul (normalizationMatrix 1 u) B)
      (Kernel.transpose (normalizationMatrix 1 u))=
      Kernel.mul (Kernel.mul (diagonalKernel 1 (imaginaryUnit*z))
        (sectorTransfer (basisA z hz) B))
        (diagonalKernel 1 (-imaginaryUnit/z)) := by
  funext a b
  cases a <;> cases b <;>
    simp [normalizationMatrix,matrix,Kernel.mul_apply,Kernel.transpose,
      diagonalKernel,sectorTransfer,conjugate,basisA,UA,UAInv,InvertibleKernel.symm,
      Signature.disequality] <;>
    field_simp [hz] <;> ring_nf <;> simp only [square,imaginaryUnit_sq] <;> ring

theorem normalization_anti (z u c t : AlgebraicComplex) (hz : z≠0) (hu : u≠0)
    (square : u^2=2) (B : Kernel AlgebraicComplex)
    (exactTransfer : sectorTransfer (basisA z hz) B=scale c (S t)) :
    (denseNormalization 1 u one_ne_zero hu).action (kernelSignature B)=
      kernelSignature (matrix 0 (-imaginaryUnit*c*t/z) (imaginaryUnit*c*z) 0) := by
  rw [InvertibleKernel.action,coordinateAction_kernelSignature]
  change kernelSignature (Kernel.mul (Kernel.mul (normalizationMatrix 1 u) B)
    (Kernel.transpose (normalizationMatrix 1 u)))=_
  rw [normalization_from_sector z u hz hu square B,exactTransfer]
  apply congrArg kernelSignature
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.mul_apply,diagonalKernel,scale,S,R,matrix,Signature.disequality] <;> ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedAntiAlgebra
end
