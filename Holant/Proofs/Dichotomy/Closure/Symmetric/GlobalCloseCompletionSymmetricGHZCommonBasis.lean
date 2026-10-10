import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4CommonBasis
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZSource
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorCriterion

/-! A retained Gram row transports a whole ordinary common basis through an
arbitrary invertible GHZ frame. The mandatory original equality edge is
reconstructed by the proved symmetric-binary pullback; it is not inferred
from membership of the transformed vertices alone. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZCommonBasis
open Holant Holant.Tractable
namespace E
export GlobalCloseCompletionEq4CommonBasis (transpose edge edge_matrix edge_symmetric)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false

def pulled (R B : InvertibleKernel) : InvertibleKernel :=
  (B.symm.comp (E.edge R)).comp (E.transpose B.symm)

theorem pulled_symmetric (R B : InvertibleKernel) :
    Kernel.transpose (pulled R B).matrix=(pulled R B).matrix := by
  simp only [pulled,InvertibleKernel.comp,E.transpose,InvertibleKernel.symm,
    Kernel.transpose_mul,Kernel.transpose_transpose]
  rw [E.edge_symmetric]
  simp only [Kernel.mul_assoc]

theorem pulled_action (R B : InvertibleKernel) :
    B.symm.action (kernelSignature (Kernel.pullback Signature.equality R.matrix))=
      kernelSignature (pulled R B).matrix := by
  rw [←E.edge_matrix]
  exact coordinateAction_kernelSignature B.inverse (E.edge R).matrix

theorem sandwich (R B : InvertibleKernel) :
    Kernel.mul (Kernel.mul (E.edge B).matrix (pulled R B).matrix) (E.edge B).matrix=
      Kernel.pullback Signature.equality (R.comp B).matrix := by
  have cancel : Kernel.mul (Kernel.transpose B.inverse) (Kernel.transpose B.matrix)=Signature.equality := by
    rw [←Kernel.transpose_mul,B.matrix_inverse,Kernel.transpose_equality]
  simp only [E.edge,pulled,E.transpose,InvertibleKernel.comp,InvertibleKernel.symm,
    Kernel.pullback,Kernel.transpose_mul,Kernel.mul_assoc]
  simp only [Kernel.equality_mul]
  rw [←Kernel.mul_assoc B.matrix B.inverse,B.matrix_inverse,Kernel.equality_mul,
    ←Kernel.mul_assoc (Kernel.transpose B.inverse) (Kernel.transpose B.matrix),cancel,Kernel.equality_mul]

theorem isCommonBasis (C F H : SignatureFamily AlgebraicComplex)
    (memberClass : C∈({affineClass,productClass,localAffineClass} : Set (SignatureFamily AlgebraicComplex)))
    (R B : InvertibleKernel) (included : familyAction R.symm F⊆H)
    (gram : (⟨2,kernelSignature (Kernel.pullback Signature.equality R.matrix)⟩ : AnySignature AlgebraicComplex)∈H)
    (basis : IsCommonBasis C H B) : IsCommonBasis C F (R.comp B) := by
  refine ⟨?_,?_⟩
  · have edge : (⟨2,kernelSignature (E.edge B).matrix⟩ : AnySignature AlgebraicComplex)∈C := by
      rw [E.edge_matrix]
      exact basis.1
    have row : (⟨2,kernelSignature (pulled R B).matrix⟩ : AnySignature AlgebraicComplex)∈C := by
      rw [←pulled_action]
      exact basis.2 _ gram
    have h:=symmetric_binary_pullback C memberClass (E.edge B) (pulled R B) edge row
      (E.edge_symmetric B) (pulled_symmetric R B)
    rwa [sandwich] at h
  · intro f hf
    have h:=basis.2 _ (included ⟨f,hf,rfl⟩)
    simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action] using h

theorem gram_nonzero (R : InvertibleKernel) : kernelSignature (Kernel.pullback Signature.equality R.matrix)≠0 := by
  intro zero
  have h:=congrFun₂ (E.edge R).matrix_inverse false false
  have vanishes (p q : Bool) : (E.edge R).matrix p q=0 := by
    rw [E.edge_matrix]
    exact congrFun zero ![p,q]
  simp [Kernel.mul_apply,vanishes,Signature.equality] at h

theorem commonTransformable (C F H : SignatureFamily AlgebraicComplex)
    (memberClass : C∈({affineClass,productClass,localAffineClass} : Set (SignatureFamily AlgebraicComplex)))
    (finite : F.Finite) (R : InvertibleKernel) (included : familyAction R.symm F⊆H)
    (gram : (⟨2,kernelSignature (Kernel.pullback Signature.equality R.matrix)⟩ : AnySignature AlgebraicComplex)∈H)
    (positive : CommonTransformable C (preprocess H)) : CommonTransformable C (preprocess F) := by
  obtain ⟨_,B,basis⟩:=positive
  refine ⟨finite.subset (fun _ h=>h.1),R.comp B,?_⟩
  apply isCommonBasis C (preprocess F) (preprocess H) memberClass R B _ _ basis
  · rintro f ⟨g,⟨hg,arity,nonzero⟩,rfl⟩
    exact ⟨included ⟨g,hg,rfl⟩,arity,fun zero=>nonzero ((Conformal.action_eq_zero_iff R.symm g.2).mp zero)⟩
  · exact ⟨gram,by change 0<2; decide,gram_nonzero R⟩

theorem tract (F H : SignatureFamily AlgebraicComplex) (finite : F.Finite)
    (R : InvertibleKernel) (included : familyAction R.symm F⊆H)
    (gram : (⟨2,kernelSignature (Kernel.pullback Signature.equality R.matrix)⟩ : AnySignature AlgebraicComplex)∈H)
    (eq4 : (⟨4,StableHigherCurrentAnchorCriterion.eq4⟩ : AnySignature AlgebraicComplex)∈H)
    (positive : Tract H) : Tract F := by
  have cases:= (StableHigherCurrentAnchorCriterion.tract_iff_one_common_basis eq4).mp positive
  rcases cases with affine|product|localAffine
  · have h:=commonTransformable affineClass F H (by simp) finite R included gram affine
    exact ⟨h.1,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · have h:=commonTransformable productClass F H (by simp) finite R included gram product
    exact ⟨h.1,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩
  · have h:=commonTransformable localAffineClass F H (by simp) finite R included gram localAffine
    exact ⟨h.1,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZCommonBasis
end
