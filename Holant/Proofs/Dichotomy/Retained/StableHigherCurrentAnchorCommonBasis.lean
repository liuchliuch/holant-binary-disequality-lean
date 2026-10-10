import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorCriterion
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorPins
import Holant.Tractable.Conformal.CommonBasis

/-! Positive whole-family closure through the exact equality anchor. The one
ordinary basis is composed with that anchor's inverse, and the native edge
retains its actual nonzero scale. No row receives a separately selected basis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorCommonBasis
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Exact ordinary-to-native basis transport, including the edge. -/
theorem pullback_common {C F H : SignatureFamily AlgebraicComplex}
    (closed : Conformal.ScaleClosed C) (A : QuaternaryEqualityTerminal.AnchorStep F)
    (included : familyAction A.basis F ⊆ H) (common : CommonTransformable C H) :
    CommonKPresentationInKCoordinates C F := by
  obtain ⟨finite,B,edge,vertices⟩ := common
  refine ⟨(Conformal.familyAction_finite_iff A.basis F).mp (finite.subset included),
    A.basis.symm.comp B,?_,?_⟩
  · change (⟨2,kernelSignature (Kernel.pullback Signature.disequality
      (Kernel.mul A.basis.inverse B.matrix))⟩ : AnySignature AlgebraicComplex) ∈ C
    rw [pullback_mul,A.edge_exact,Conformal.pullback_scale]
    exact closed 2 _ edge A.edgeScale
  · intro f hf
    have h := vertices ⟨f.1,A.basis.action f.2⟩ (included ⟨f,hf,rfl⟩)
    simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action,
      InvertibleKernel.symm_symm] using h

/-- All original current rows remain in the preprocessed ordinary family. -/
theorem preprocessed_inclusion {F H : SignatureFamily AlgebraicComplex}
    (A : QuaternaryEqualityTerminal.AnchorStep F) (preprocessed : Preprocessed F)
    (included : familyAction A.basis F ⊆ H) : familyAction A.basis F ⊆ preprocess H := by
  intro f hf
  exact ⟨included hf,Conformal.preprocessed_familyAction A.basis preprocessed f hf⟩

/-- The positive terminal for an entire anchored current family. The Eq4
obstruction derives the class choice; its single basis then classifies every
original current signature and the actual native disequality edge together. -/
theorem native_common_of_ordinary_tract {F H : SignatureFamily AlgebraicComplex}
    (A : QuaternaryEqualityTerminal.AnchorStep F) (preprocessed : Preprocessed F)
    (included : familyAction A.basis F ⊆ H)
    (eq4 : (⟨4,StableHigherCurrentAnchorCriterion.eq4⟩ : AnySignature AlgebraicComplex) ∈ H)
    (tract : Tract H) :
    CommonKPresentationInKCoordinates affineClass F ∨
      CommonKPresentationInKCoordinates productClass F ∨
      CommonKPresentationInKCoordinates localAffineClass F := by
  have inclusion := preprocessed_inclusion A preprocessed included
  rcases (StableHigherCurrentAnchorCriterion.tract_iff_one_common_basis eq4).mp tract with
    affine | product | localAffine
  · exact Or.inl (pullback_common Conformal.affineClass_scaleClosed A inclusion affine)
  · exact Or.inr (Or.inl (pullback_common Conformal.productClass_scaleClosed A inclusion product))
  · exact Or.inr (Or.inr (pullback_common Conformal.localAffineClass_scaleClosed A inclusion localAffine))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorCommonBasis
end
