import Holant.Proofs.Closure.ClosureNativePresentation

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeProductCriterion
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem criterion (F : SignatureFamily AlgebraicComplex) (finite : F.Finite)
    (product : ∀f∈F,Product f.2) : TractX (familyAction sourceKBasis F) := by
  apply ClosureNativePresentation.tractX_forward_product
  refine ⟨finite,InvertibleKernel.identity,?_,?_⟩
  · change Product (kernelSignature (Kernel.pullback Signature.disequality InvertibleKernel.identity.matrix))
    have hp : Product (kernelSignature Signature.disequality):=product_disequality 0 1
    simpa [InvertibleKernel.identity,Kernel.pullback] using hp
  · intro f hf
    change Product (InvertibleKernel.identity.symm.action f.2)
    simpa using product f hf

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeProductCriterion
end
