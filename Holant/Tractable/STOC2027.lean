import Holant.Tractable.Conformal.TensorAlternatives

/-!
The reduced tractability predicates in the November 2026 STOC manuscript.

`ReTract` is the new name of the existing four-clause ordinary-edge predicate.
`ReTractX` states the four clauses directly for disequality edges. In its three
transformability branches, one common matrix transforms both the native edge
and every signature. The coordinate bridge below is an algebraic proof, with
the same zero/nullary preprocessing on both sides; no dichotomy is imported.
-/

namespace Holant.Tractable
noncomputable section

/-- The manuscript's four reduced cases with ordinary equality edges. -/
abbrev ReTract (F : SignatureFamily AlgebraicComplex) : Prop := TractX F

/-- The four reduced cases with the actual disequality-edge common basis. -/
def ReTractXCore (F : SignatureFamily AlgebraicComplex) : Prop :=
  ArityTwoAlternative F ∨ CommonKPresentationInKCoordinates affineClass F ∨
  CommonKPresentationInKCoordinates productClass F ∨
  CommonKPresentationInKCoordinates localAffineClass F

/-- Native disequality-edge reduced criterion, after deleting precisely zero
and nullary signatures as prescribed in the manuscript. -/
def ReTractX (F : SignatureFamily AlgebraicComplex) : Prop :=
  (preprocess F).Finite ∧ ReTractXCore (preprocess F)

/-- The same common matrix, converted by `M = K U`, gives the ordinary-edge
presentation of the entire `K`-image. The edge is retained in both directions. -/
theorem commonKPresentation_iff_commonTransformable_K
    (C F : SignatureFamily AlgebraicComplex) :
    CommonKPresentationInKCoordinates C F ↔
      CommonTransformable C (familyAction sourceKBasis F) := by
  constructor
  · rintro ⟨hfin, U, hedge, hfamily⟩
    refine ⟨hfin.image _, sourceKBasis.comp U, ?_, ?_⟩
    · simpa only [InvertibleKernel.comp, pullback_mul, sourceKBasis_pullback] using hedge
    · rintro f ⟨g, hg, rfl⟩
      simpa only [InvertibleKernel.comp_symm, InvertibleKernel.comp_action,
        InvertibleKernel.symm_action_action] using hfamily g hg
  · rintro ⟨hfin, M, hedge, hfamily⟩
    refine ⟨(Conformal.familyAction_finite_iff _ _).mp hfin,
      sourceKBasis.symm.comp M, ?_, ?_⟩
    · have he : Kernel.pullback Signature.disequality
          (sourceKBasis.symm.comp M).matrix =
          Kernel.pullback Signature.equality M.matrix := by
        rw [← sourceKBasis_pullback, ← pullback_mul]
        change Kernel.pullback Signature.equality
          (Kernel.mul sourceKBasis.matrix (Kernel.mul sourceKBasis.inverse M.matrix)) = _
        rw [← Kernel.mul_assoc, sourceKBasis.matrix_inverse, Kernel.equality_mul]
      simpa only [he] using hedge
    · intro g hg
      simpa only [InvertibleKernel.comp_symm, InvertibleKernel.comp_action,
        InvertibleKernel.symm_symm] using
        hfamily ⟨g.1, sourceKBasis.action g.2⟩ ⟨g, hg, rfl⟩

/-- All four cases transform together. Tensor decompositions are transported
by the actual invertible map, and the three classes share the edge bridge. -/
theorem reTractXCore_iff_tractXCore_K (F : SignatureFamily AlgebraicComplex) :
    ReTractXCore F ↔ TractXCore (familyAction sourceKBasis F) := by
  unfold ReTractXCore TractXCore
  rw [← Conformal.arityTwo_iff_map sourceKBasis F,
    ← commonKPresentation_iff_commonTransformable_K affineClass F,
    ← commonKPresentation_iff_commonTransformable_K productClass F,
    ← commonKPresentation_iff_commonTransformable_K localAffineClass F]

/-- The manuscript's explicit coordinate identity
`ReTract_X(F) ↔ ReTract(K F)`, including its preprocessing convention. -/
theorem reTractX_iff_reTract_K (F : SignatureFamily AlgebraicComplex) :
    ReTractX F ↔ ReTract (familyAction sourceKBasis F) := by
  unfold ReTractX ReTract TractX
  rw [Conformal.preprocess_familyAction, Conformal.familyAction_finite_iff,
    reTractXCore_iff_tractXCore_K]

end
end Holant.Tractable
