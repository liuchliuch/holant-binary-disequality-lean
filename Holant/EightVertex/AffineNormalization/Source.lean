import Holant.EightVertex.AffineNormalization.DiagonalAssembly

/-! Proposition4.5 in the manuscript's algebraic common-K-basis convention.
The full diagonal witness and all three exact support alternatives are derived
from the actual affine transformed edge and quaternary. -/
namespace Holant.EightVertex.AffineNormalization
open Holant.Tractable Holant.EightVertex.ProductAnchor
open Holant.Certificates.AffineEndpoint Holant.Certificates.AffineReference
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure DiagonalCertificate (M : Signature AlgebraicComplex 4) where
  d0 : AlgebraicComplex
  d1 : AlgebraicComplex
  d0_ne_zero : d0≠0
  d1_ne_zero : d1≠0
  gamma : AlgebraicComplex
  gamma_ne_zero : gamma≠0
  reference : Signature AlgebraicComplex 4
  reference_affine : Affine reference
  reference_zero : reference zeroWord=1
  reference_support : ReferenceSupport reference
  reconstruction : M=gamma • Signature.coordinateAction (fun _ => diagonalKernel d0 d1) reference

namespace DiagonalCertificate
variable {M : Signature AlgebraicComplex 4} (C : DiagonalCertificate M)

def basis : InvertibleKernel := diagonalBasis C.d0 C.d1 C.d0_ne_zero C.d1_ne_zero
def normalized : Signature AlgebraicComplex 4 := C.basis.symm.action M

theorem normalized_eq : C.normalized=C.gamma • C.reference := by
  unfold normalized
  apply (congrArg C.basis.symm.action C.reconstruction).trans
  change Signature.coordinateAction (fun _ => C.basis.inverse)
    (C.gamma • C.basis.action C.reference) = _
  rw [coordinateAction_scale]
  change C.gamma • C.basis.symm.action (C.basis.action C.reference)=_
  rw [InvertibleKernel.symm_action_action]

theorem normalized_affine : Affine C.normalized := by
  rw [C.normalized_eq]
  exact C.reference_affine.scale C.gamma

theorem normalized_support : ReferenceSupport C.normalized := by
  rw [C.normalized_eq]
  exact reference_support_scale C.reference_support C.gamma C.gamma_ne_zero

theorem pullback : Kernel.pullback Signature.disequality C.basis.matrix =
    fun a b => (C.d0*C.d1)*Signature.disequality a b := diagonal_pullback C.d0 C.d1

theorem conformal : XConformal C.basis :=
  ⟨C.d0*C.d1,mul_ne_zero C.d0_ne_zero C.d1_ne_zero,C.pullback⟩

theorem original_support (x : Fin 4 → Bool) : M x≠0 ↔ C.normalized x≠0 := by
  have he : M=C.basis.action C.normalized := (C.basis.action_symm_action M).symm
  rw [congrFun he x]
  change Signature.coordinateAction (fun _ => diagonalKernel C.d0 C.d1) C.normalized x≠0 ↔ _
  rw [coordinateAction_diagonal]
  exact mul_ne_zero_iff.trans (and_iff_right (diagonalCoefficient_ne_zero C.d0_ne_zero C.d1_ne_zero x))

theorem endpoint_pure (hs : endpointSupport C.normalized) : PureEquality M := by
  apply endpoint_reference_pure
  intro x
  exact (C.original_support x).trans (hs x)

theorem normalized_support_sizes : supportSize C.normalized=2 ∨
    supportSize C.normalized=4 ∨ supportSize C.normalized=8 :=
  source_A4_support_cases C.normalized C.normalized_support

end DiagonalCertificate

theorem source_affine_quaternary_certificate (M : Signature AlgebraicComplex 4)
    (hM : EndpointEven M)
    (hA : CommonKPresentationInKCoordinates affineClass {⟨4,M⟩}) :
    Nonempty (DiagonalCertificate M) := by
  obtain ⟨_,U,hE,hF⟩ := hA
  have hf : Affine (U.symm.action M) := hF ⟨4,M⟩ (by simp)
  obtain ⟨a,d,gamma,ha,hd,hgamma,h,haff,h0,hsupp,he⟩ :=
    affine_diagonal_reconstruction M hM U hE hf
  exact ⟨⟨a,d,ha,hd,gamma,hgamma,h,haff,h0,hsupp,he⟩⟩

/-- The exact diagonal-normalization and conformal-edge conclusion of the
printed proposition, with algebraic nonzero diagonal entries. -/
theorem source_diagonal_affine_witness (M : Signature AlgebraicComplex 4)
    (hM : EndpointEven M)
    (hA : CommonKPresentationInKCoordinates affineClass {⟨4,M⟩}) :
    ∃ D : InvertibleKernel, (∃ a d : AlgebraicComplex,a≠0 ∧ d≠0 ∧ D.matrix=diagonalKernel a d) ∧
      Affine (D.symm.action M) ∧ XConformal D ∧ ReferenceSupport (D.symm.action M) ∧
      (endpointSupport (D.symm.action M) → PureEquality M) := by
  obtain ⟨C⟩ := source_affine_quaternary_certificate M hM hA
  exact ⟨C.basis,⟨C.d0,C.d1,C.d0_ne_zero,C.d1_ne_zero,rfl⟩,
    C.normalized_affine,C.conformal,C.normalized_support,C.endpoint_pure⟩

end
end Holant.EightVertex.AffineNormalization
