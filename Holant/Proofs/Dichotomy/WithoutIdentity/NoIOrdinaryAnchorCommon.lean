import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorCommonBasis

/-! Exact whole-family native common-basis return with the prescribed
zero/nullary preprocessing, for a genuine anchor in the complete family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryAnchorCommon
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false

theorem common {C F H : SignatureFamily AlgebraicComplex}
    (closed : Conformal.ScaleClosed C) (A : QuaternaryEqualityTerminal.AnchorStep F)
    (finite : F.Finite) (included : familyAction A.basis F⊆H)
    (good : CommonTransformable C (preprocess H)) :
    CommonKPresentationInKCoordinates C (preprocess F) := by
  obtain ⟨_,B,edge,vertices⟩:=good
  refine ⟨finite.subset (fun _ hf=>hf.1),A.basis.symm.comp B,?_,?_⟩
  · change (⟨2,kernelSignature (Kernel.pullback Signature.disequality
      (Kernel.mul A.basis.inverse B.matrix))⟩ : AnySignature AlgebraicComplex)∈C
    rw [pullback_mul,A.edge_exact,Conformal.pullback_scale]
    exact closed 2 _ edge A.edgeScale
  · intro f hf
    have preprocessed:=Conformal.preprocessed_familyAction A.basis (preprocess_preprocessed F)
      ⟨f.1,A.basis.action f.2⟩ ⟨f,hf,rfl⟩
    have h:=vertices ⟨f.1,A.basis.action f.2⟩ ⟨included ⟨f,hf.1,rfl⟩,preprocessed⟩
    simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action,InvertibleKernel.symm_symm] using h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryAnchorCommon
end
