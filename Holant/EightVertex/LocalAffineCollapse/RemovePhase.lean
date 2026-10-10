import Holant.EightVertex.LocalAffineCollapse.BalancedParity
import Holant.EightVertex.LocalAffineCollapse.Phase.Assembly

/-! Remove the derived algebraic eighth-root column phase from an arbitrary
complex basis, retaining exact edge and signature coefficients. -/
namespace Holant.EightVertex.LocalAffineCollapse
open Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
noncomputable section
set_option backward.isDefEq.respectTransparency false

def removeColumnPhase (T : ComplexBasis) (rho : AlgebraicComplex) (hr : rho≠0) : ComplexBasis :=
  T.comp (complexDiagonalBasis 1 ((rho:ℂ)⁻¹) one_ne_zero
    (inv_ne_zero (by exact_mod_cast hr)))

theorem removed_inverse_matrix (T : ComplexBasis) (rho : AlgebraicComplex) (hr : rho≠0) :
    (removeColumnPhase T rho hr).inverse =
      Kernel.mul (embedMatrix (diagonalKernel 1 rho)) T.inverse := by
  apply congrArg (fun A => Kernel.mul A T.inverse)
  funext x y
  cases x <;> cases y <;> simp [complexDiagonalBasis,complexDiagonal,embedMatrix,diagonalKernel]

theorem removed_matrix (T : ComplexBasis) (a c : ℂ) (rho : AlgebraicComplex) (hr : rho≠0)
    (hT : T.matrix=complexBalanced a c rho) :
    (removeColumnPhase T rho hr).matrix=complexBalanced a c 1 := by
  have hrC : (rho:ℂ)≠0 := by exact_mod_cast hr
  funext x y
  cases x <;> cases y <;>
    simp [removeColumnPhase,ComplexBasis.comp,complexDiagonalBasis,hT,complexBalanced,
      complexMatrix,Kernel.mul_apply,complexDiagonal,hrC]

def raised (N : Signature AlgebraicComplex 4) (rho : AlgebraicComplex) :
    Signature AlgebraicComplex 4 := fun x => rho^Holant.weight x*N x

theorem raised_action (N : Signature AlgebraicComplex 4) (rho : AlgebraicComplex) :
    Signature.coordinateAction (fun _ => diagonalKernel 1 rho) N=raised N rho := by
  rw [coordinateAction_diagonal]
  funext x
  rw [diagonalCoefficient_eq_weight]
  simp [raised]

theorem removed_signature (T : ComplexBasis) (rho : AlgebraicComplex) (hr : rho≠0)
    (M : Signature ℂ 4) (N : Signature AlgebraicComplex 4)
    (hN : embedSignature N=T.symm.action M) :
    (removeColumnPhase T rho hr).symm.action M=embedSignature (raised N rho) := by
  change Signature.coordinateAction (fun _ => (removeColumnPhase T rho hr).inverse) M = _
  rw [removed_inverse_matrix,←Signature.coordinateAction_comp]
  change Signature.coordinateAction (fun _ => embedMatrix (diagonalKernel 1 rho))
    (T.symm.action M)=_
  rw [←hN,←embed_action,raised_action]

theorem removed_edge (T : ComplexBasis) (a c : ℂ) (rho : AlgebraicComplex) (hr : rho≠0)
    (hT : T.matrix=complexBalanced a c rho) (p : AlgebraicComplex) (hp : (p:ℂ)=2*a*c) :
    embedMatrix (diagonal p (-p)) =
      Kernel.pullback Signature.disequality (removeColumnPhase T rho hr).matrix := by
  rw [removed_matrix T a c rho hr hT,complex_pullback_entries]
  funext x y
  cases x <;> cases y <;>
    simp [embedMatrix,diagonal,complexBalanced,complexMatrix,hp] <;> ring

theorem affine_removed_edge (p : AlgebraicComplex) :
    Affine (kernelSignature (diagonal p (-p))) := by
  simpa using affine_diagonal_phase p (2 : ZMod 4)

theorem phase_reduction (T : ComplexBasis) (E : Kernel AlgebraicComplex)
    (hE : embedMatrix E=Kernel.pullback Signature.disequality T.matrix)
    (hEL : LocalAffine (kernelSignature E))
    (M : Signature ℂ 4) (hM : ∀x,Holant.weight x%2=1 → M x=0)
    (N : Signature AlgebraicComplex 4) (hN : embedSignature N=T.symm.action M)
    (hNL : LocalAffine N) :
    ∃rho : AlgebraicComplex,∃hr : rho≠0,rho^8=1 ∧ Affine (raised N rho) ∧
      embedSignature (raised N rho)=(removeColumnPhase T rho hr).symm.action M ∧
      embedMatrix (diagonal (E false false) (-(E false false)))=
        Kernel.pullback Signature.disequality (removeColumnPhase T rho hr).matrix := by
  obtain ⟨a,c,ha,hc,rho,hr8,hT,hp⟩ := complex_localAffine_matrix T E hE hEL
  have hr : rho≠0 := by intro hz; simpa [hz] using hr8
  have hsignature := removed_signature T rho hr M N hN
  have hsym := balanced_inverse_complement (removeColumnPhase T rho hr) a c
    (removed_matrix T a c rho hr hT) M hM
  have hcomp : ∀x,raised N rho (complementWord x)=raised N rho x := by
    intro x
    apply Subtype.ext
    exact (congrFun hsignature (complementWord x)).symm.trans
      ((hsym x).trans (congrFun hsignature x))
  refine ⟨rho,hr,hr8,?_,hsignature.symm,removed_edge T a c rho hr hT _ hp⟩
  exact Phase.affine_of_localAffine_complement N rho hNL hr hr8 hcomp

end
end Holant.EightVertex.LocalAffineCollapse
