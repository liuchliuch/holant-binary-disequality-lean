import Holant.Tractable.Criteria
import Holant.Tractable.Anchor.MatrixActions

/-! Exact bridge from a family with native disequality edges to its forward-K
ordinary Holant image. `kCoordinates` in the frozen criterion means inverse K;
therefore the family classified here is `familyAction sourceKBasis Gamma`.
All statements are structural predicates, not algorithms or complexity claims. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureNativePresentation
open Holant Holant.Tractable

/-- Inverse action undoes a whole-family forward action, with original arities. -/
theorem inverse_familyAction (B : InvertibleKernel)
    (F : SignatureFamily AlgebraicComplex) :
    familyAction B.symm (familyAction B F) = F := by
  unfold familyAction
  rw [Set.image_image]
  have h : (fun f : AnySignature AlgebraicComplex =>
      (⟨f.1, B.symm.action (B.action f.2)⟩ : AnySignature AlgebraicComplex)) = id := by
    funext f
    cases f
    simp
  rw [h, Set.image_id]

theorem finite_familyAction_iff (B : InvertibleKernel)
    (F : SignatureFamily AlgebraicComplex) :
    (familyAction B F).Finite ↔ F.Finite := by
  constructor
  · intro h
    have hi := h.image (fun f : AnySignature AlgebraicComplex =>
      (⟨f.1, B.symm.action f.2⟩ : AnySignature AlgebraicComplex))
    change (familyAction B.symm (familyAction B F)).Finite at hi
    rwa [inverse_familyAction] at hi
  · intro h
    exact h.image _

/-- This is the fixed coordinate conversion, not a second native K action. -/
theorem kCoordinates_forward (Gamma : SignatureFamily AlgebraicComplex) :
    kCoordinates (familyAction sourceKBasis Gamma) = Gamma :=
  inverse_familyAction sourceKBasis Gamma

/-- The SAME U acts on native Gamma and on the native X edge. The additional
K inverse in the computational-coordinate definition cancels only its forward
K image, not U and not an unrelated computational input family. -/
theorem commonKPresentation_forward_iff
    (C Gamma : SignatureFamily AlgebraicComplex) :
    CommonKPresentation C (familyAction sourceKBasis Gamma) ↔
      CommonKPresentationInKCoordinates C Gamma := by
  constructor
  · rintro ⟨hfin, U, hedge, hf⟩
    refine ⟨(finite_familyAction_iff _ _).mp hfin, U, hedge, ?_⟩
    intro f hfg
    have hx := hf ⟨f.1, sourceKBasis.action f.2⟩ ⟨f, hfg, rfl⟩
    simpa only [InvertibleKernel.symm_action_action] using hx
  · rintro ⟨hfin, U, hedge, hf⟩
    refine ⟨(finite_familyAction_iff _ _).mpr hfin, U, hedge, ?_⟩
    rintro _ ⟨f, hfg, rfl⟩
    simpa only [InvertibleKernel.symm_action_action] using hf f hfg

/-- The ordinary common basis is K U, whose inverse is U inverse K inverse. -/
theorem computational_basis_action (U : InvertibleKernel) {n : ℕ}
    (f : Signature AlgebraicComplex n) :
    (sourceKBasis.comp U).symm.action (sourceKBasis.action f) = U.symm.action f := by
  simp only [InvertibleKernel.comp_symm, InvertibleKernel.comp_action,
    InvertibleKernel.symm_action_action]

/-- The edge follows the same K U, with ordinary transpose and no conjugation. -/
theorem computational_basis_edge (U : InvertibleKernel) :
    Kernel.pullback Signature.equality (sourceKBasis.comp U).matrix =
      Kernel.pullback Signature.disequality U.matrix := by
  simp only [InvertibleKernel.comp, pullback_mul, sourceKBasis_pullback]

/-- Exact source/native equivalence, including finiteness and one common basis. -/
theorem commonTransformable_forward_iff
    (C Gamma : SignatureFamily AlgebraicComplex) :
    CommonTransformable C (familyAction sourceKBasis Gamma) ↔
      CommonKPresentationInKCoordinates C Gamma :=
  (commonTransformable_iff_commonKPresentation _ _).trans
    (commonKPresentation_forward_iff C Gamma)

/-- A real native witness directly installs the explicit ordinary basis K U. -/
theorem basis_forward {C Gamma : SignatureFamily AlgebraicComplex}
    (U : InvertibleKernel) (h : IsCommonKBasis C Gamma U) :
    IsCommonBasis C (familyAction sourceKBasis Gamma) (sourceKBasis.comp U) := by
  refine ⟨?_, ?_⟩
  · simpa only [computational_basis_edge] using h.1
  · rintro _ ⟨f, hf, rfl⟩
    simpa only [computational_basis_action] using h.2 f hf

private theorem preprocessed_common {C Gamma : SignatureFamily AlgebraicComplex}
    (h : CommonKPresentationInKCoordinates C Gamma) :
    CommonTransformable C (preprocess (familyAction sourceKBasis Gamma)) :=
  ((commonTransformable_forward_iff C Gamma).mpr h).mono_family (fun _ hf => hf.1)

theorem tractX_forward_affine {Gamma : SignatureFamily AlgebraicComplex}
    (h : CommonKPresentationInKCoordinates affineClass Gamma) :
    TractX (familyAction sourceKBasis Gamma) := by
  have hc := preprocessed_common h
  exact ⟨hc.1, Or.inr (Or.inl hc)⟩

theorem tractX_forward_product {Gamma : SignatureFamily AlgebraicComplex}
    (h : CommonKPresentationInKCoordinates productClass Gamma) :
    TractX (familyAction sourceKBasis Gamma) := by
  have hc := preprocessed_common h
  exact ⟨hc.1, Or.inr (Or.inr (Or.inl hc))⟩

theorem tractX_forward_localAffine {Gamma : SignatureFamily AlgebraicComplex}
    (h : CommonKPresentationInKCoordinates localAffineClass Gamma) :
    TractX (familyAction sourceKBasis Gamma) := by
  have hc := preprocessed_common h
  exact ⟨hc.1, Or.inr (Or.inr (Or.inr hc))⟩

/-- Orientation regression: forward K sends native equality to Z, not equality. -/
theorem forward_equality_is_z :
    sourceKBasis.action (kernelSignature Signature.equality) = zAnchor := by
  rw [← sourceKBasis_symm_action_zAnchor, InvertibleKernel.action_symm_action]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureNativePresentation
