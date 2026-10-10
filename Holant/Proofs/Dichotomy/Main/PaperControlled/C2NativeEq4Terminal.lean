import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinary
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinFiniteEq4
import Holant.Proofs.Closure.ClosureNativePresentation

/-! Full public criterion for any genuine finite native Eq4 source. Zero and
nullary rows are handled by the existing preprocessing predicate; no extra
preprocessed-family hypothesis is required at this boundary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2NativeEq4Terminal
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace F
export GlobalCloseCompletionKleinFiniteEq4 (Input family data output)
end F
namespace E
export GlobalCloseCompletionBEqualityCSP (current_included)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val)) (D : F.Input G)
variable (out : GlobalCloseCompletionBPrimeEq4.Output D.table)

theorem common (target : TargetClass)
    (h : CommonTransformable target.family (preprocess (GenericLiteralXSource.family G (F.data G D out)))) :
    CommonKPresentationInKCoordinates target.family (preprocess (F.family G D)) := by
  obtain ⟨_,V,basis⟩ := h
  have x : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈
      preprocess (GenericLiteralXSource.family G (F.data G D out)) := by
    refine ⟨GenericLiteralXSource.family_x G (F.data G D out),by decide,?_⟩
    intro zero
    have hz := congrFun zero ![false,true]
    simp [kernelSignature,Signature.disequality] at hz
  have native := GlobalCloseCompletionEq4CommonBasis.target_native_of_ordinary target _ V x basis
  refine ⟨(Set.finite_range _).subset (fun _ hf=>hf.1),V,native.1,?_⟩
  intro f hf
  exact native.2 f ⟨E.current_included D.table out hf.1,hf.2⟩

include out in
theorem classified_output : Tract (familyAction sourceKBasis (F.family G D)) ∨
    PaperControlledHardness.Original G := by
  rcases PaperControlledOrdinary.literalX_classified G (F.data G D out) with tract|hard
  · left
    rcases (StableHigherCurrentAnchorCriterion.tract_iff_one_common_basis
      (GenericLiteralXSource.family_eq4 G (F.data G D out))).mp tract with affine|product|localAffine
    · have h := (ClosureNativePresentation.commonTransformable_forward_iff _ _).mpr (common G D out .affine affine)
      rw [←Conformal.preprocess_familyAction] at h
      exact (show TractX (familyAction sourceKBasis (F.family G D)) from ⟨h.1,Or.inr (Or.inl h)⟩).tract
    · have h := (ClosureNativePresentation.commonTransformable_forward_iff _ _).mpr (common G D out .product product)
      rw [←Conformal.preprocess_familyAction] at h
      exact (show TractX (familyAction sourceKBasis (F.family G D)) from ⟨h.1,Or.inr (Or.inr (Or.inl h))⟩).tract
    · have h := (ClosureNativePresentation.commonTransformable_forward_iff _ _).mpr (common G D out .localAffine localAffine)
      rw [←Conformal.preprocess_familyAction] at h
      exact (show TractX (familyAction sourceKBasis (F.family G D)) from ⟨h.1,Or.inr (Or.inr (Or.inr h))⟩).tract
  · exact Or.inr hard

include D in
theorem classified (actual : Gadget.RealizesUpTo (F.family G D) .disequality
    (Holant.EightVertex.ProductAnchor.equalityFour (K:=AlgebraicComplex))) :
    Tract (familyAction sourceKBasis (F.family G D)) ∨ PaperControlledHardness.Original G := by
  obtain ⟨out⟩ := F.output G D actual
  exact classified_output G D out

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2NativeEq4Terminal
end
