import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4CommonBasis
import Holant.Tractable.Anchor
import Holant.Tractable.Conformal

/-! Literal X makes the ordinary-to-native wire swap faithful to the full
seven-clause criterion. The same class and same common basis transport the
entire family and its mandatory edge. The file name of the existing common
basis lemma does not impose an equality-four hypothesis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsCriterion
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false

theorem common_to_native (C F : SignatureFamily AlgebraicComplex)
    (member : C∈({affineClass,productClass,localAffineClass} : Set (SignatureFamily AlgebraicComplex)))
    (x : (⟨2,xAnchor⟩ : AnySignature AlgebraicComplex)∈F)
    (tract : CommonTransformable C F) : CommonTransformable C (familyAction sourceKBasis F) := by
  obtain ⟨finite,B,basis⟩:=tract
  have native:=GlobalCloseCompletionEq4CommonBasis.native_of_ordinary C F member B x basis
  refine ⟨finite.image _,sourceKBasis.comp B,?_,?_⟩
  · simpa only [InvertibleKernel.comp,pullback_mul,sourceKBasis_pullback] using native.1
  · rintro f ⟨g,hg,rfl⟩
    simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action,
      InvertibleKernel.symm_action_action] using native.2 g hg

/-- All four surviving ordinary clauses give the corresponding native
criterion. No unary, equality-four, or per-signature criterion is assumed. -/
theorem tract_to_native (F : SignatureFamily AlgebraicComplex)
    (x : (⟨2,xAnchor⟩ : AnySignature AlgebraicComplex)∈F)
    (tract : Tract F) : Tract (familyAction sourceKBasis F) := by
  have reduced:=(tract_iff_tractX_of_xAnchor_mem x).mp tract
  have xp : (⟨2,xAnchor⟩ : AnySignature AlgebraicComplex)∈preprocess F :=
    ⟨x,by decide,xAnchor_ne_zero⟩
  rw [Tract,Conformal.preprocess_familyAction]
  refine ⟨tract.1.image _,TractXCore.tractCore ?_⟩
  rcases reduced.2 with small|affine|product|localAffine
  · exact Or.inl (Conformal.arityTwo_map sourceKBasis small)
  · exact Or.inr (Or.inl (common_to_native affineClass (preprocess F) (by simp) xp affine))
  · exact Or.inr (Or.inr (Or.inl (common_to_native productClass (preprocess F) (by simp) xp product)))
  · exact Or.inr (Or.inr (Or.inr (common_to_native localAffineClass (preprocess F) (by simp) xp localAffine)))

theorem negative (old newer : SignatureFamily AlgebraicComplex)
    (included : familyAction sourceKBasis.symm old⊆newer)
    (x : (⟨2,xAnchor⟩ : AnySignature AlgebraicComplex)∈newer)
    (rejected : ¬Tract old) : ¬Tract newer := by
  intro tract
  apply rejected
  apply (tract_to_native newer x tract).mono_family
  intro f hf
  refine ⟨⟨f.1,sourceKBasis.symm.action f.2⟩,included ⟨f,hf,rfl⟩,?_⟩
  simp only [InvertibleKernel.action_symm_action,Sigma.eta]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsCriterion
end
