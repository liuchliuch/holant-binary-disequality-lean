import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorLocalCandidates
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorAffineBasisCandidates

/-! Exact local-affine common-basis test in sixteen normalized bases. The
nonzero scalar is removed simultaneously from every vertex and the actual
ordinary edge, retaining the local-affine class in every arity. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorLocalCriterion
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open StableHigherCurrentAnchorLocalCandidates
namespace A
export StableHigherCurrentAnchorAffineBasisCandidates (rescale action_scale basis_eq_of_inverse)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem candidate_determinant (opposite : Bool) (q : Fin 8) :
    determinant (candidate opposite q) ≠ 0 := by
  cases opposite <;>
    simp [candidate,determinant,diagonal,antidiagonal,pow_ne_zero _ zetaEight_ne_zero]

def candidateBasis (opposite : Bool) (q : Fin 8) : InvertibleKernel :=
  invertibleOfDeterminant (candidate opposite q) (candidate_determinant opposite q)

/-- Scalar normalization preserves the one common local-affine basis,
including its genuine square edge scale and inverse arity vertex scales. -/
theorem rescale_common {H : SignatureFamily AlgebraicComplex} (B : InvertibleKernel)
    (c : AlgebraicComplex) (hc : c≠0) (hB : IsCommonBasis localAffineClass H B) :
    IsCommonBasis localAffineClass H (A.rescale B c hc) := by
  constructor
  · have he : Kernel.pullback Signature.equality (A.rescale B c hc).matrix=
        fun a b=>c^2*Kernel.pullback Signature.equality B.matrix a b := by
      funext a b
      simp only [A.rescale,Kernel.pullback,Kernel.mul_apply,Kernel.transpose]
      ring
    change LocalAffine (kernelSignature (Kernel.pullback Signature.equality (A.rescale B c hc).matrix))
    rw [he]
    exact LocalAffine.scale hB.1 (c^2)
  · intro f hf
    change LocalAffine (Signature.coordinateAction (fun _ a b=>c⁻¹*B.inverse a b) f.2)
    rw [A.action_scale]
    exact LocalAffine.scale (hB.2 f hf) (c⁻¹^f.1)

/-- Both implications use one shared member of the sixteen-element family.
The row and edge predicates remain explicit; candidates are not assumed good. -/
theorem common_transformable_iff_candidates {H : SignatureFamily AlgebraicComplex}
    (h0 : (⟨1,L.pin false⟩ : AnySignature AlgebraicComplex)∈H)
    (h1 : (⟨1,L.pin true⟩ : AnySignature AlgebraicComplex)∈H) :
    CommonTransformable localAffineClass H ↔ H.Finite ∧
      ∃opposite : Bool,∃q : Fin 8,
        IsCommonBasis localAffineClass H (candidateBasis opposite q) := by
  constructor
  · rintro ⟨hfin,B,hB⟩
    obtain ⟨c,hc,opposite,q,he⟩ := common_basis_candidates B h0 h1 hB
    let D := A.rescale B c⁻¹ (inv_ne_zero hc)
    have hm : D.matrix=(candidateBasis opposite q).matrix := by
      funext a b
      change c⁻¹*B.matrix a b=candidate opposite q a b
      rw [he]
      simp [hc]
    have hd : D=candidateBasis opposite q := by
      have hi := A.basis_eq_of_inverse D.symm (candidateBasis opposite q).symm hm
      simpa only [InvertibleKernel.symm_symm] using congrArg InvertibleKernel.symm hi
    refine ⟨hfin,opposite,q,?_⟩
    rw [←hd]
    exact rescale_common B c⁻¹ (inv_ne_zero hc) hB
  · rintro ⟨hfin,opposite,q,hB⟩
    exact ⟨hfin,candidateBasis opposite q,hB⟩

theorem candidate_index_card : Fintype.card (Bool × Fin 8)=16 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorLocalCriterion
end
