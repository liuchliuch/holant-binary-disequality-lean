import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0RetainedX

/-! The actual original-family gate implementing the inverse Hadamard
native edge. Its complete-group representative and exact nonzero multiplier
are retained; neither a coordinate change nor a signed edge is a free gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0CoordinateGate
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open scoped Matrix
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace R
export GlobalCloseCompletionA0RetainedX (key multiplier multiplier_nonzero key_mapped)
end R
namespace W
export GlobalCloseCompletionA0Workfield (basis)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

abbrev gate : Kernel AlgebraicComplex :=
  ClosureSourceRows.representative G P torsion (R.key G P torsion N)

theorem actual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality
    (kernelSignature (gate G P torsion N)) :=
  ClosureSourceRows.representative_actual G P torsion (R.key G P torsion N)

theorem gate_exact : gate G P torsion N=
    scale (2*R.multiplier G P torsion N) (diagonalKernel 1 (-1)) := by
  have hh : W.basis.symm.action (kernelSignature (gate G P torsion N))=
      kernelSignature (scale (R.multiplier G P torsion N) Signature.disequality) := by
    rw [transport_signature]
    exact congrArg kernelSignature (R.key_mapped G P torsion N)
  have back := congrArg W.basis.action hh
  rw [InvertibleKernel.action_symm_action] at back
  rw [InvertibleKernel.action,coordinateAction_kernelSignature] at back
  funext b c
  have point := congrFun back ![b,c]
  change gate G P torsion N b c=_ at point
  rw [point]
  cases b <;> cases c <;>
    simp [W.basis,GlobalCloseCompletionA0Workfield.basis,ClosureMarkedDihedralA0.basis,
      ClosureMarkedCyclic.basis,basisA,UA,scale,diagonalKernel,
      Kernel.mul_apply,Kernel.transpose,kernelSignature,Signature.disequality] <;> ring

def coefficient : AlgebraicComplex := -1/(4*R.multiplier G P torsion N)

theorem coefficient_nonzero : coefficient G P torsion N≠0 :=
  div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (R.multiplier_nonzero G P torsion N))

theorem inverse_edge : Kernel.pullback Signature.disequality W.basis.inverse=
    scale (coefficient G P torsion N)
      (Kernel.mul (Kernel.mul Signature.disequality (gate G P torsion N)) Signature.disequality) := by
  rw [gate_exact]
  funext b c
  cases b <;> cases c <;>
    simp [Kernel.pullback,W.basis,GlobalCloseCompletionA0Workfield.basis,ClosureMarkedDihedralA0.basis,
      ClosureMarkedCyclic.basis,basisA,UAInv,scale,diagonalKernel,
      Kernel.mul_apply,Kernel.transpose,Signature.disequality,coefficient] <;>
    field_simp [R.multiplier_nonzero G P torsion N] <;> ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0CoordinateGate
end
