import Holant.Proofs.Dichotomy.WithoutIdentity.NoISuppliedIdentityData
import Holant.Proofs.Closure.ClosureNativePresentation
import Holant.Proofs.Algorithms.TractXRestore

/-! A native-X-preserving source basis transports the entire positive
criterion back in one common basis, including the original zero/nullary rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeCriterionReturn
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable (F H : SignatureFamily AlgebraicComplex) (finiteF : F.Finite) (finiteH : H.Finite)
variable (B : InvertibleKernel)
variable (native : Kernel.pullback Signature.disequality B.matrix=Signature.disequality)
variable (included : familyAction B.symm F⊆H)

include finiteF B native included in
theorem common (C : SignatureFamily AlgebraicComplex)
    (positive : CommonTransformable C (familyAction sourceKBasis H)) :
    CommonKPresentationInKCoordinates C F := by
  obtain ⟨_,U,edge,rows⟩:=(ClosureNativePresentation.commonTransformable_forward_iff C H).mp positive
  refine ⟨finiteF,B.comp U,?_,?_⟩
  · simpa only [InvertibleKernel.comp,pullback_mul,native] using edge
  · intro f member
    have h:=rows _ (included ⟨f,member,rfl⟩)
    simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action] using h

include finiteF finiteH B native included in
theorem criterion (positive : TractX (familyAction sourceKBasis H)) :
    TractX (familyAction sourceKBasis F) := by
  have core:=TractXRestore.source_criterion_core
    ((Conformal.familyAction_finite_iff sourceKBasis H).mpr finiteH) positive
  rcases core with small|affine|product|localAffine
  · have smallH:=(Conformal.arityTwo_iff_map sourceKBasis H).mpr small
    have smallF:=(Conformal.arityTwo_iff_map B.symm F).mpr (smallH.mono_family included)
    have smallK:=Conformal.arityTwo_map sourceKBasis smallF
    exact ⟨((Conformal.familyAction_finite_iff sourceKBasis F).mpr finiteF).subset (fun _ h=>h.1),
      Or.inl (smallK.mono_family (fun _ h=>h.1))⟩
  · exact ClosureNativePresentation.tractX_forward_affine (common F H finiteF B native included _ affine)
  · exact ClosureNativePresentation.tractX_forward_product (common F H finiteF B native included _ product)
  · exact ClosureNativePresentation.tractX_forward_localAffine (common F H finiteF B native included _ localAffine)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeCriterionReturn
end
