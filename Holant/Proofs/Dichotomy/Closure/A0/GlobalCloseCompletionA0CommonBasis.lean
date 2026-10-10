import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0Workfield
import Holant.Tractable.Conformal.CommonBasis
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4CommonBasis

/-! Recover the exact original native-X edge in the accumulated Hadamard
and ordinary-test basis. The source row is the actual inverse edge Z/2,
not literal X. Symmetric binary pullback and its recorded factor four give
2 Bᵀ Z B in the same Affine/Product/LocalAffine class. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0CommonBasis
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace E
export GlobalCloseCompletionEq4CommonBasis (transpose edge edge_matrix edge_symmetric)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
abbrev basis := GlobalCloseCompletionA0Workfield.basis

def native : InvertibleKernel := (basis.symm.comp bitFlipBasis).comp (E.transpose basis.symm)
def anchor (B : InvertibleKernel) : InvertibleKernel := (B.symm.comp native).comp (E.transpose B.symm)

theorem native_action : basis.symm.action (kernelSignature Signature.disequality)=
    kernelSignature native.matrix := coordinateAction_kernelSignature basis.inverse Signature.disequality

theorem native_symmetric : Kernel.transpose native.matrix=native.matrix := by
  simp [native,E.transpose,GlobalCloseCompletionEq4CommonBasis.transpose,
    InvertibleKernel.comp,InvertibleKernel.symm,bitFlipBasis,Kernel.transpose_mul,Kernel.mul_assoc]

theorem anchor_symmetric (B : InvertibleKernel) : Kernel.transpose (anchor B).matrix=(anchor B).matrix := by
  simp only [anchor,InvertibleKernel.comp,E.transpose,GlobalCloseCompletionEq4CommonBasis.transpose,
    InvertibleKernel.symm,Kernel.transpose_mul,Kernel.transpose_transpose,native_symmetric,Kernel.mul_assoc]

theorem anchor_action (B : InvertibleKernel) :
    B.symm.action (kernelSignature native.matrix)=kernelSignature (anchor B).matrix :=
  coordinateAction_kernelSignature B.inverse native.matrix

theorem sandwich (B : InvertibleKernel) :
    Kernel.mul (Kernel.mul (E.edge B).matrix (anchor B).matrix) (E.edge B).matrix=
      Kernel.pullback native.matrix B.matrix := by
  have cancel : Kernel.mul (Kernel.transpose B.inverse) (Kernel.transpose B.matrix)=Signature.equality := by
    rw [←Kernel.transpose_mul,B.matrix_inverse,Kernel.transpose_equality]
  simp only [E.edge,GlobalCloseCompletionEq4CommonBasis.edge,anchor,E.transpose,
    GlobalCloseCompletionEq4CommonBasis.transpose,InvertibleKernel.comp,InvertibleKernel.symm,
    Kernel.pullback,Kernel.mul_assoc]
  rw [←Kernel.mul_assoc B.matrix B.inverse,B.matrix_inverse,Kernel.equality_mul,
    ←Kernel.mul_assoc (Kernel.transpose B.inverse) (Kernel.transpose B.matrix),cancel,Kernel.equality_mul]

theorem original_edge : sectorEdge basis=scale 4 native.matrix := by
  funext b c
  cases b <;> cases c <;>
    norm_num [sectorEdge,native,basis,GlobalCloseCompletionA0Workfield.basis,
      ClosureMarkedDihedralA0.basis,ClosureMarkedCyclic.basis,Holant.Marked.basisA,
      Holant.Marked.UA,Holant.Marked.UAInv,E.transpose,GlobalCloseCompletionEq4CommonBasis.transpose,
      InvertibleKernel.comp,InvertibleKernel.symm,bitFlipBasis,Kernel.pullback,Kernel.mul_apply,
      Kernel.transpose,Signature.disequality,scale]

theorem scale_closed (target : TargetClass) : Conformal.ScaleClosed target.family := by
  cases target
  · exact Conformal.affineClass_scaleClosed
  · exact Conformal.productClass_scaleClosed
  · exact Conformal.localAffineClass_scaleClosed

theorem native_edge (target : TargetClass) (H : SignatureFamily AlgebraicComplex) (B : InvertibleKernel)
    (hx : (⟨2,basis.symm.action (kernelSignature Signature.disequality)⟩ : AnySignature AlgebraicComplex)∈H)
    (hb : IsCommonBasis target.family H B) :
    (⟨2,kernelSignature (Kernel.pullback Signature.disequality (basis.comp B).matrix)⟩ :
      AnySignature AlgebraicComplex)∈target.family := by
  have ordinary : (⟨2,kernelSignature (E.edge B).matrix⟩ : AnySignature AlgebraicComplex)∈target.family := by
    rw [E.edge_matrix]
    exact hb.1
  have resource : (⟨2,kernelSignature (anchor B).matrix⟩ : AnySignature AlgebraicComplex)∈target.family := by
    rw [←anchor_action,←native_action]
    exact hb.2 _ hx
  have member : target.family∈({affineClass,productClass,localAffineClass} :
      Set (SignatureFamily AlgebraicComplex)) := by cases target <;> simp [TargetClass.family]
  have h := symmetric_binary_pullback target.family member (E.edge B) (anchor B)
    ordinary resource (E.edge_symmetric B) (anchor_symmetric B)
  rw [sandwich] at h
  change (⟨2,kernelSignature (Kernel.pullback Signature.disequality (Kernel.mul basis.matrix B.matrix))⟩ :
    AnySignature AlgebraicComplex)∈target.family
  rw [pullback_mul,show Kernel.pullback Signature.disequality basis.matrix=scale 4 native.matrix from original_edge]
  change (⟨2,kernelSignature (Kernel.pullback (fun b c => 4*native.matrix b c) B.matrix)⟩ :
    AnySignature AlgebraicComplex)∈target.family
  rw [Conformal.pullback_scale]
  exact scale_closed target 2 _ h 4

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0CommonBasis
end
