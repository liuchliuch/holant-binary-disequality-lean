import Holant.EightVertex.LocalAffineCollapse.RemovePhase

/-! If the given witness is algebraic, the same phase deletion produces an
actual algebraic invertible witness. No algebraic-witness existence theorem is
assumed, and the original matrix's normalization is preserved explicitly. -/
namespace Holant.EightVertex.LocalAffineCollapse
open Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
noncomputable section
set_option backward.isDefEq.respectTransparency false

def algebraicColumnPhase (rho : AlgebraicComplex) (hr : rho≠0) : InvertibleKernel where
  matrix := diagonalKernel 1 rho⁻¹
  inverse := diagonalKernel 1 rho
  matrix_inverse := by
    funext x y
    cases x <;> cases y <;> simp [Kernel.mul_apply,diagonalKernel,Signature.equality,hr]
  inverse_matrix := by
    funext x y
    cases x <;> cases y <;> simp [Kernel.mul_apply,diagonalKernel,Signature.equality,hr]

def algebraicRemove (U : InvertibleKernel) (rho : AlgebraicComplex) (hr : rho≠0) :
    InvertibleKernel := U.comp (algebraicColumnPhase rho hr)

theorem algebraicRemove_matrix (U : InvertibleKernel) (rho : AlgebraicComplex) (hr : rho≠0) :
    embedMatrix (algebraicRemove U rho hr).matrix=
      (removeColumnPhase (ofAlgebraic U) rho hr).matrix := by
  change embedMatrix (Kernel.mul U.matrix (diagonalKernel 1 rho⁻¹)) =
    Kernel.mul (embedMatrix U.matrix) (complexDiagonal 1 ((rho:ℂ)⁻¹))
  rw [embedMatrix_mul,embedMatrix_diagonal]
  rfl

theorem algebraicRemove_inverse (U : InvertibleKernel) (rho : AlgebraicComplex) (hr : rho≠0) :
    embedMatrix (algebraicRemove U rho hr).inverse=
      (removeColumnPhase (ofAlgebraic U) rho hr).inverse := by
  rw [removed_inverse_matrix]
  exact embedMatrix_mul (diagonalKernel 1 rho) U.inverse

theorem algebraic_phase_reduction (U : InvertibleKernel) (M : Signature AlgebraicComplex 4)
    (hM : ∀x,Holant.weight x%2=1 → M x=0)
    (hE : LocalAffine (kernelSignature (Kernel.pullback Signature.disequality U.matrix)))
    (hN : LocalAffine (U.symm.action M)) :
    ∃rho : AlgebraicComplex,∃hr : rho≠0,rho^8=1 ∧
      Affine (kernelSignature (Kernel.pullback Signature.disequality (algebraicRemove U rho hr).matrix)) ∧
      Affine ((algebraicRemove U rho hr).symm.action M) := by
  have hMcomplex : ∀x,Holant.weight x%2=1 → embedSignature M x=0 := by
    intro x hx
    simp [embedSignature,hM x hx]
  obtain ⟨rho,hr,hr8,hA,hN0,hE0⟩ := phase_reduction (ofAlgebraic U)
    (Kernel.pullback Signature.disequality U.matrix) (embedMatrix_pullback U.matrix) hE
    (embedSignature M) hMcomplex (U.symm.action M) (embed_action_basis U.symm M) hN
  let U0 := algebraicRemove U rho hr
  have hsignature : U0.symm.action M=raised (U.symm.action M) rho := by
    have hc : embedSignature (U0.symm.action M)=embedSignature (raised (U.symm.action M) rho) := by
      rw [embed_action_basis]
      change Signature.coordinateAction (fun _ => embedMatrix U0.inverse) (embedSignature M)=_
      rw [algebraicRemove_inverse U rho hr]
      exact hN0.symm
    funext x
    exact Subtype.ext (congrFun hc x)
  have hedge : Kernel.pullback Signature.disequality U0.matrix=
      diagonal ((Kernel.pullback Signature.disequality U.matrix) false false)
        (-((Kernel.pullback Signature.disequality U.matrix) false false)) := by
    have hc := (embedMatrix_pullback U0.matrix).trans
      ((congrArg (Kernel.pullback Signature.disequality) (algebraicRemove_matrix U rho hr)).trans hE0.symm)
    funext a b
    exact Subtype.ext (congrFun (congrFun hc a) b)
  refine ⟨rho,hr,hr8,?_,?_⟩
  · change Affine (kernelSignature (Kernel.pullback Signature.disequality U0.matrix))
    rw [hedge]
    exact affine_removed_edge _
  · change Affine (U0.symm.action M)
    rw [hsignature]
    exact hA

end
end Holant.EightVertex.LocalAffineCollapse
