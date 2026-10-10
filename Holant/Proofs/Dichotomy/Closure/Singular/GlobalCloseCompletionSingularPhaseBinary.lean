import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBDenseAnchorX
import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularAffineBinary

/-! Actual diagonal phases in the cycle's exact dense normalization produce
traceless symmetric binaries. Two distinct retained phases suffice to choose
one with nonzero off-diagonal, with all representative multipliers retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularPhaseBinary
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.EightVertex.ProductAnchor
namespace B
export GlobalCloseCompletionSingularAffineBinary (matrix square_eq_of_fourth_eq sandwich sandwich_nonzero)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false

def diagonal (r u mu t : AlgebraicComplex) : AlgebraicComplex := mu*u^2/4*(1+t/r^2)
def offDiagonal (r u mu t : AlgebraicComplex) : AlgebraicComplex := mu*imaginaryUnit*u^2/4*(1-t/r^2)

theorem normalization_phase (r u mu t : AlgebraicComplex) (hr : r≠0) (hu : u≠0) :
    (denseNormalization r u hr hu).action (kernelSignature (scale mu (Holant.Marked.R t)))=
      kernelSignature (B.matrix (diagonal r u mu t) (offDiagonal r u mu t)) := by
  rw [InvertibleKernel.action,coordinateAction_kernelSignature]
  apply congrArg kernelSignature
  funext b c
  cases b <;> cases c <;>
    simp [denseNormalization,normalizationMatrix,Holant.EightVertex.ProductAnchor.matrix,
      scale,Holant.Marked.R,diagonalKernel,Kernel.mul_apply,Kernel.transpose,B.matrix,
      diagonal,offDiagonal]
  all_goals field_simp [hr]
  all_goals ring_nf
  all_goals simp [imaginaryUnit_sq]; ring

theorem sum_squares (r u mu t : AlgebraicComplex) (hr : r≠0) (square : u^2=2*r) :
    (diagonal r u mu t)^2+(offDiagonal r u mu t)^2=mu^2*t := by
  dsimp [diagonal,offDiagonal]
  rw [square]
  field_simp [hr]
  ring_nf
  simp [imaginaryUnit_sq]; ring

theorem nonsingular (r u mu t : AlgebraicComplex) (hr : r≠0) (hm : mu≠0) (ht : t≠0)
    (square : u^2=2*r) : (diagonal r u mu t)^2+(offDiagonal r u mu t)^2≠0 := by
  rw [sum_squares r u mu t hr square]
  exact mul_ne_zero (pow_ne_zero _ hm) ht

theorem offDiagonal_nonzero (r u mu t : AlgebraicComplex) (hr : r≠0) (hu : u≠0)
    (hm : mu≠0) (different : t≠r^2) : offDiagonal r u mu t≠0 := by
  unfold offDiagonal
  apply mul_ne_zero
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero hm imaginaryUnit_ne_zero) (pow_ne_zero _ hu)) (by norm_num)
  · intro hz
    have h : t/r^2=1 := (sub_eq_zero.mp hz).symm
    have ht : t=r^2 := (div_eq_one_iff_eq (pow_ne_zero _ hr)).mp h
    exact different ht

theorem choose_phase (r omega : AlgebraicComplex) (distinct : omega≠1) :
    ∃t : AlgebraicComplex,(t=1 ∨ t=omega) ∧ t≠r^2 := by
  by_cases h : (1 : AlgebraicComplex)=r^2
  · exact ⟨omega,Or.inr rfl,fun bad=>distinct (bad.trans h.symm)⟩
  · exact ⟨1,Or.inl rfl,h⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularPhaseBinary
end
