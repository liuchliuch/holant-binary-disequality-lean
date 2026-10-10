import Holant.Proofs.Closure.ClosureNativePresentation
import Holant.Tractable.Conformal.MatrixSupport

/-! A single diagonal phase for the entire native family includes the actual
native edge in its common Affine basis. No per-row choice is substituted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativePhaseCriterion
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace D
def diagonal (a b : AlgebraicComplex) : Kernel AlgebraicComplex :=
  fun p q => if p=q then (if p then b else a) else 0
def diagonalBasis (a b : AlgebraicComplex) (ha : a≠0) (hb : b≠0) : InvertibleKernel where
  matrix := diagonal a b
  inverse := diagonal a⁻¹ b⁻¹
  matrix_inverse := by
    funext p q
    cases p <;> cases q <;> simp [diagonal,Kernel.mul_apply,Signature.equality,ha,hb]
  inverse_matrix := by
    funext p q
    cases p <;> cases q <;> simp [diagonal,Kernel.mul_apply,Signature.equality,ha,hb]
end D

def basis (r : AlgebraicComplex) (nonzero : r ≠ 0) : InvertibleKernel :=
  D.diagonalBasis 1 r⁻¹ one_ne_zero (inv_ne_zero nonzero)

theorem action (r : AlgebraicComplex) (nonzero : r ≠ 0)
    {n : ℕ} (f : Signature AlgebraicComplex n) :
    (basis r nonzero).symm.action f = fun x => r ^ weight x * f x := by
  have mat : (basis r nonzero).inverse = diagonalKernel 1 r := by
    funext p q
    cases p <;> cases q <;> simp [basis,D.diagonalBasis,D.diagonal,diagonalKernel]
  change Signature.coordinateAction (fun _ => (basis r nonzero).inverse) f = _
  rw [mat,coordinateAction_diagonal]
  funext x
  congr 1
  change (∏ j, if x j then r else 1) = r ^ (∑ j, if x j then 1 else 0)
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  cases x j <;> simp

theorem edge (r : AlgebraicComplex) (nonzero : r ≠ 0) :
    Affine (kernelSignature (Kernel.pullback Signature.disequality (basis r nonzero).matrix)) := by
  let S : AffineSystem 2 := ⟨1,fun _ _ => 1,fun _ => 1⟩
  have holds (x : Fin 2 → Bool) : S.Holds x ↔ x 0 ≠ x 1 := by
    change (∀ _ : Fin 1, (∑ j : Fin 2, (1 : ZMod 2) * bitValue (ZMod 2) (x j)) = 1) ↔ _
    simp only [Fin.forall_fin_one,Fin.sum_univ_two,one_mul]
    cases x 0 <;> cases x 1 <;> decide
  convert (affine_indicator S).scale r⁻¹ using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature,Kernel.pullback,Kernel.mul_apply,Kernel.transpose,basis,D.diagonalBasis,D.diagonal,
      Signature.disequality,Fintype.sum_bool,h0,h1,holds]

theorem criterion (F : SignatureFamily AlgebraicComplex) (finite : F.Finite)
    (r : AlgebraicComplex) (nonzero : r ≠ 0)
    (all : ∀ f ∈ F, Affine (fun x => r ^ weight x * f.2 x)) :
    TractX (familyAction sourceKBasis F) := by
  apply ClosureNativePresentation.tractX_forward_affine
  refine ⟨finite,basis r nonzero,edge r nonzero,?_⟩
  intro f hf
  change Affine ((basis r nonzero).symm.action f.2)
  rw [action]
  exact all f hf

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativePhaseCriterion
end
