import Holant.Proofs.Closure.FrontierSplitClosure
import Holant.Proofs.Closure.ClosureNativePresentation


noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierNativeClosure
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FrontierCommonPresentation
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- CURRENT native family: one U, native-X edge and every current saved leaf. -/
theorem relative_current_native_k_presentation (P : Palette G) (target : TargetClass)
    (U : InvertibleKernel)
    (edge : (⟨2,kernelSignature (Kernel.pullback Signature.disequality U.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (leaves : CurrentFrontierClosure.LocalCurrentTheorems G P (leafPredicate G target.family U)) :
    CommonKPresentationInKCoordinates target.family (CurrentFrontierClosure.currentFamily G P) := by
  refine ⟨CurrentFrontierClosure.currentFamily_finite G P,U,edge,?_⟩
  rintro _ ⟨f,hf,rfl⟩
  exact CurrentFrontierClosure.relative_current_closure G P (leafPredicate G target.family U)
    (FrontierSplitClosure.splitClosed_target G target U) leaves f hf

/-- Independent original saved-family version, preserving the same native edge. -/
theorem relative_original_native_k_presentation (P : Palette G) (target : TargetClass)
    (U : InvertibleKernel)
    (edge : (⟨2,kernelSignature (Kernel.pullback Signature.disequality U.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (leaves : FrontierClosure.LocalLeafTheorems G P (leafPredicate G target.family U)) :
    CommonKPresentationInKCoordinates target.family (originalFamily G) := by
  refine ⟨originalFamily_finite G,U,edge,?_⟩
  rintro _ ⟨f,hf,rfl⟩
  exact FrontierClosure.relative_saved_closure G P (leafPredicate G target.family U)
    (FrontierSplitClosure.splitClosed_target G target U) leaves f hf

/-- CURRENT local theorems restrict to the original saved roots with THIS U. -/
theorem relative_current_native_restricts_original (P : Palette G) (target : TargetClass)
    (U : InvertibleKernel)
    (edge : (⟨2,kernelSignature (Kernel.pullback Signature.disequality U.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (leaves : CurrentFrontierClosure.LocalCurrentTheorems G P (leafPredicate G target.family U)) :
    CommonKPresentationInKCoordinates target.family (originalFamily G) := by
  refine ⟨originalFamily_finite G,U,edge,?_⟩
  rintro _ ⟨f,hf,rfl⟩
  exact CurrentFrontierClosure.relative_current_closure G P (leafPredicate G target.family U)
    (FrontierSplitClosure.splitClosed_target G target U) leaves f
    (CurrentOccurrences.original_family_retained G P hf)

/-- The exact computational family is K·CURRENT, using the single basis K U. -/
theorem relative_current_native_tractx (P : Palette G) (target : TargetClass)
    (U : InvertibleKernel)
    (edge : (⟨2,kernelSignature (Kernel.pullback Signature.disequality U.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (leaves : CurrentFrontierClosure.LocalCurrentTheorems G P (leafPredicate G target.family U)) :
    TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G P)) := by
  have h := relative_current_native_k_presentation G P target U edge leaves
  cases target with
  | affine => exact ClosureNativePresentation.tractX_forward_affine h
  | product => exact ClosureNativePresentation.tractX_forward_product h
  | localAffine => exact ClosureNativePresentation.tractX_forward_localAffine h

/-- The original saved native family has its own exact K-image criterion. -/
theorem relative_original_native_tractx (P : Palette G) (target : TargetClass)
    (U : InvertibleKernel)
    (edge : (⟨2,kernelSignature (Kernel.pullback Signature.disequality U.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (leaves : FrontierClosure.LocalLeafTheorems G P (leafPredicate G target.family U)) :
    TractX (familyAction sourceKBasis (originalFamily G)) := by
  have h := relative_original_native_k_presentation G P target U edge leaves
  cases target with
  | affine => exact ClosureNativePresentation.tractX_forward_affine h
  | product => exact ClosureNativePresentation.tractX_forward_product h
  | localAffine => exact ClosureNativePresentation.tractX_forward_localAffine h

/-- A stronger explicit witness gate: every table and the edge use THIS K U,
not independently selected per-leaf computational bases. -/
theorem relative_current_computational_basis (P : Palette G) (target : TargetClass)
    (U : InvertibleKernel)
    (edge : (⟨2,kernelSignature (Kernel.pullback Signature.disequality U.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (leaves : CurrentFrontierClosure.LocalCurrentTheorems G P (leafPredicate G target.family U)) :
    IsCommonBasis target.family (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G P))
      (sourceKBasis.comp U) := by
  apply ClosureNativePresentation.basis_forward U
  refine ⟨edge,?_⟩
  rintro _ ⟨f,hf,rfl⟩
  exact CurrentFrontierClosure.relative_current_closure G P (leafPredicate G target.family U)
    (FrontierSplitClosure.splitClosed_target G target U) leaves f hf

end Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierNativeClosure
end
