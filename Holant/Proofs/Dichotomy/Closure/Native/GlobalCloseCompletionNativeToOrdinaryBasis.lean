import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4CommonBasis

/-! Dual same-basis compatibility. An actual literal I vertex converts a
native-X common basis to an ordinary-I common basis, with no change of basis
between retained rows and no assumed inverse-closure theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionNativeToOrdinaryBasis
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierCommonPresentation
open GlobalCloseCompletionEq4CommonBasis (transpose)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option Elab.async false

def edge (B : InvertibleKernel) : InvertibleKernel := ((transpose B).comp bitFlipBasis).comp B

def anchor (B : InvertibleKernel) : InvertibleKernel := B.symm.comp (transpose B.symm)

theorem edge_matrix (B : InvertibleKernel) :
    (edge B).matrix=Kernel.pullback Signature.disequality B.matrix := by
  simp [edge,transpose,InvertibleKernel.comp,bitFlipBasis,Kernel.pullback,Kernel.mul_assoc]

theorem edge_symmetric (B : InvertibleKernel) :
    Kernel.transpose (edge B).matrix=(edge B).matrix := by
  simp [edge,transpose,InvertibleKernel.comp,bitFlipBasis,Kernel.transpose_mul,Kernel.mul_assoc]

theorem anchor_symmetric (B : InvertibleKernel) :
    Kernel.transpose (anchor B).matrix=(anchor B).matrix := by
  simp [anchor,transpose,InvertibleKernel.comp,InvertibleKernel.symm,Kernel.transpose_mul]

theorem anchor_action (B : InvertibleKernel) :
    B.symm.action (kernelSignature Signature.equality)=kernelSignature (anchor B).matrix := by
  simpa [anchor,transpose,InvertibleKernel.comp,InvertibleKernel.symm,InvertibleKernel.action] using
    coordinateAction_kernelSignature B.inverse Signature.equality

theorem sandwich (B : InvertibleKernel) :
    Kernel.mul (Kernel.mul (edge B).matrix (anchor B).matrix) (edge B).matrix=
      Kernel.pullback Signature.equality B.matrix := by
  have cancel : Kernel.mul (Kernel.transpose B.inverse) (Kernel.transpose B.matrix)=
      Signature.equality := by
    rw [←Kernel.transpose_mul,B.matrix_inverse,Kernel.transpose_equality]
  simp only [edge,anchor,transpose,InvertibleKernel.comp,InvertibleKernel.symm,bitFlipBasis,
    Kernel.pullback,Kernel.mul_assoc]
  rw [←Kernel.mul_assoc B.matrix B.inverse,B.matrix_inverse,Kernel.equality_mul,
    ←Kernel.mul_assoc (Kernel.transpose B.inverse) (Kernel.transpose B.matrix),
    cancel,Kernel.equality_mul]
  simp [←Kernel.mul_assoc]

theorem ordinary_of_native (C F : SignatureFamily AlgebraicComplex)
    (memberClass : C∈({affineClass,productClass,localAffineClass} : Set (SignatureFamily AlgebraicComplex)))
    (B : InvertibleKernel)
    (identity : (⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)∈F)
    (basis : IsCommonKBasis C F B) : IsCommonBasis C F B := by
  refine ⟨?_,basis.2⟩
  have native : (⟨2,kernelSignature (edge B).matrix⟩ : AnySignature AlgebraicComplex)∈C := by
    rw [edge_matrix]
    exact basis.1
  have ordinary : (⟨2,kernelSignature (anchor B).matrix⟩ : AnySignature AlgebraicComplex)∈C := by
    rw [←anchor_action]
    exact basis.2 _ identity
  have h := symmetric_binary_pullback C memberClass (edge B) (anchor B)
    native ordinary (edge_symmetric B) (anchor_symmetric B)
  rwa [sandwich] at h

theorem target_ordinary_of_native (target : TargetClass) (F : SignatureFamily AlgebraicComplex)
    (B : InvertibleKernel)
    (identity : (⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)∈F)
    (basis : IsCommonKBasis target.family F B) : IsCommonBasis target.family F B := by
  apply ordinary_of_native target.family F _ B identity basis
  cases target <;> simp [TargetClass.family]

theorem common_ordinary_of_native (target : TargetClass) (F : SignatureFamily AlgebraicComplex)
    (identity : (⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)∈F)
    (common : CommonKPresentationInKCoordinates target.family F) : CommonTransformable target.family F := by
  obtain ⟨finite,B,basis⟩ := common
  exact ⟨finite,B,target_ordinary_of_native target F B identity basis⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionNativeToOrdinaryBasis
end
