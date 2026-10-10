import Holant.Proofs.Recognition.UniformTractXSemantics
import Holant.Tractable.Conformal.CommonBasis

/-!
# Exact native four-clause semantics on untransformed original coefficients

The native criterion is literally `TractX (familyAction sourceKBasis G)`.
Its common-basis clauses are decided by the existing raw A/P/L systems with
mandatory disequality edge. The fixed normalized source K acts forwards here;
this is not the inverse-K entry convention used by EO support recognition.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformNativeTractXSemantics
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.MainChain.TransformRecognition
open UniformTensorDecisionBranch
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} (arity : Fin s → ℕ)

/-- One shared basis and the exact mandatory edge, transported by source K. -/
theorem common_forward_iff (C F : SignatureFamily AlgebraicComplex) :
    CommonTransformable C (familyAction sourceKBasis F) ↔
      CommonKPresentationInKCoordinates C F := by
  rw [commonTransformable_iff_commonKPresentation]
  unfold CommonKPresentation CommonKPresentationInKCoordinates
  rw [Conformal.familyAction_finite_iff]
  simp only [IsCommonKBasis,familyAction,Set.forall_mem_image,
    InvertibleKernel.symm_action_action]

abbrev family (d : Data s arity) := familyAction sourceKBasis (AffineBranch.indexedFamily d.G)

def affine (d : Data s arity) : Bool :=
  RawAffineRecognitionSource.answer arity d.input (UniformTractXSemantics.valid arity d) true
def product (d : Data s arity) : Bool :=
  RawProductRecognitionSource.answer arity d.input (UniformTractXSemantics.valid arity d) true
def localAffine (d : Data s arity) : Bool :=
  RawLocalAffineRecognitionSource.answer arity d.input (UniformTractXSemantics.valid arity d) true

theorem affine_correct (d : Data s arity) :
    affine arity d=true ↔ CommonTransformable affineClass (family arity d) := by
  rw [affine,RawAffineRecognitionSource.answer_correct arity d.input
    (UniformTractXSemantics.valid arity d) true d.G d.represented,
    common_forward_iff,AffineBranch.commonK_iff_shared]
  change AffineBranch.Shared d.G Signature.disequality (algebraMap AlgebraicComplex ℂ) ↔ _
  exact ⟨AffineBranch.descend d.G Signature.disequality,
    UniformTractXSemantics.affine_lift d.G Signature.disequality⟩

theorem product_correct (d : Data s arity) :
    product arity d=true ↔ CommonTransformable productClass (family arity d) := by
  rw [product,RawProductRecognitionSource.answer_correct arity d.input
    (UniformTractXSemantics.valid arity d) true d.G d.represented,
    common_forward_iff,ProductBranch.commonK_iff_templates]
  change ProductBranch.SharedSource d.G Signature.disequality (algebraMap AlgebraicComplex ℂ) ↔ _
  rw [ProductBranch.source_iff_templates]
  exact ⟨ProductBranch.descend_templates d.G Signature.disequality,
    UniformTractXSemantics.product_lift d.G Signature.disequality⟩

theorem localAffine_correct (d : Data s arity) :
    localAffine arity d=true ↔ CommonTransformable localAffineClass (family arity d) := by
  rw [localAffine,RawLocalAffineRecognitionSource.answer_correct arity d.input
    (UniformTractXSemantics.valid arity d) true d.G d.represented,
    common_forward_iff,LocalAffineBranch.commonK_iff_shared]
  change LocalAffineBranch.Shared d.G Signature.disequality (algebraMap AlgebraicComplex ℂ) ↔ _
  exact ⟨LocalAffineBranch.descend d.G Signature.disequality,
    UniformTractXSemantics.localAffine_lift d.G Signature.disequality⟩

/-- Arity bounds are preserved by any invertible action on every tensor factor. -/
theorem tensor_map (B : InvertibleKernel) {F : SignatureFamily AlgebraicComplex}
    (h : ArityTwoAlternative F) : ArityTwoAlternative (familyAction B F) := by
  rintro f ⟨g,hg,rfl⟩
  rcases h g hg with hz | ht
  · apply Or.inl
    change B.action g.2=0
    rw [hz]
    exact Signature.coordinateAction_zero _
  · exact Or.inr (ht.map_action B.matrix (fun _ _ h => h))

theorem tensor_iff (d : Data s arity) :
    ArityTwoAlternative (AffineBranch.indexedFamily d.G) ↔ ArityTwoAlternative (family arity d) := by
  refine ⟨tensor_map sourceKBasis,?_⟩
  intro h
  simpa only [family,Conformal.familyAction_symm_action] using tensor_map sourceKBasis.symm h

theorem tractX_iff_core (d : Data s arity) :
    TractX (family arity d) ↔ TractXCore (family arity d) := by
  have hf : (family arity d).Finite := (Conformal.familyAction_finite_iff _ _).mpr (Set.finite_range _)
  exact ⟨TractXRestore.source_criterion_core hf,
    fun h => ⟨hf.subset (fun _ hf => hf.1),UniformTractXSemantics.core_preprocess h⟩⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformNativeTractXSemantics
