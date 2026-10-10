import Holant.Tractable.SymmetricBinaryPullback
import Holant.Tractable.Anchor.MatrixActions
import Holant.Proofs.Closure.FrontierCommonPresentation

/-! A literal X row transfers one entire ordinary common basis to the native
X-edge problem. Both transformed symmetric nonsingular binaries are already
in the selected class. Their proved pullback reconstructs the mandatory native
edge in that same basis; no per-row transform or gadget is postulated. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4CommonBasis
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierCommonPresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def transpose (B : InvertibleKernel) : InvertibleKernel where
  matrix := Kernel.transpose B.matrix
  inverse := Kernel.transpose B.inverse
  matrix_inverse := by
    rw [←Kernel.transpose_mul,B.inverse_matrix,Kernel.transpose_equality]
  inverse_matrix := by
    rw [←Kernel.transpose_mul,B.matrix_inverse,Kernel.transpose_equality]

def edge (B : InvertibleKernel) : InvertibleKernel := (transpose B).comp B

def anchor (B : InvertibleKernel) : InvertibleKernel :=
  (B.symm.comp bitFlipBasis).comp (transpose B.symm)

theorem edge_matrix (B : InvertibleKernel) :
    (edge B).matrix=Kernel.pullback Signature.equality B.matrix := by
  simp [edge,transpose,InvertibleKernel.comp,Kernel.pullback]

theorem edge_symmetric (B : InvertibleKernel) :
    Kernel.transpose (edge B).matrix=(edge B).matrix := by
  simp [edge,transpose,InvertibleKernel.comp,Kernel.transpose_mul]

theorem anchor_symmetric (B : InvertibleKernel) :
    Kernel.transpose (anchor B).matrix=(anchor B).matrix := by
  simp [anchor,transpose,InvertibleKernel.comp,InvertibleKernel.symm,bitFlipBasis,
    Kernel.transpose_mul,Kernel.mul_assoc]

theorem anchor_action (B : InvertibleKernel) :
    B.symm.action (kernelSignature Signature.disequality)=kernelSignature (anchor B).matrix :=
  coordinateAction_kernelSignature B.inverse Signature.disequality

/-- The two class members reconstruct BᵀXB exactly, with ordinary transpose. -/
theorem sandwich (B : InvertibleKernel) :
    Kernel.mul (Kernel.mul (edge B).matrix (anchor B).matrix) (edge B).matrix=
      Kernel.pullback Signature.disequality B.matrix := by
  have cancel : Kernel.mul (Kernel.transpose B.inverse) (Kernel.transpose B.matrix)=
      Signature.equality := by
    rw [←Kernel.transpose_mul,B.matrix_inverse,Kernel.transpose_equality]
  simp only [edge,anchor,transpose,InvertibleKernel.comp,InvertibleKernel.symm,bitFlipBasis,
    Kernel.pullback,Kernel.mul_assoc]
  rw [←Kernel.mul_assoc B.matrix B.inverse,B.matrix_inverse,Kernel.equality_mul,
    ←Kernel.mul_assoc (Kernel.transpose B.inverse) (Kernel.transpose B.matrix),
    cancel,Kernel.equality_mul]

/-- One literal X member suffices for the exact same basis and whole family. -/
theorem native_of_ordinary (C F : SignatureFamily AlgebraicComplex)
    (memberClass : C∈({affineClass,productClass,localAffineClass} : Set (SignatureFamily AlgebraicComplex)))
    (B : InvertibleKernel)
    (x : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (basis : IsCommonBasis C F B) : IsCommonKBasis C F B := by
  refine ⟨?_,basis.2⟩
  have ordinary : (⟨2,kernelSignature (edge B).matrix⟩ : AnySignature AlgebraicComplex)∈C := by
    rw [edge_matrix]
    exact basis.1
  have native : (⟨2,kernelSignature (anchor B).matrix⟩ : AnySignature AlgebraicComplex)∈C := by
    rw [←anchor_action]
    exact basis.2 _ x
  have h := symmetric_binary_pullback C memberClass (edge B) (anchor B)
    ordinary native (edge_symmetric B) (anchor_symmetric B)
  rwa [sandwich] at h

theorem target_native_of_ordinary (target : TargetClass) (F : SignatureFamily AlgebraicComplex)
    (B : InvertibleKernel)
    (x : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (basis : IsCommonBasis target.family F B) : IsCommonKBasis target.family F B := by
  apply native_of_ordinary target.family F _ B x basis
  cases target <;> simp [TargetClass.family]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4CommonBasis
end
