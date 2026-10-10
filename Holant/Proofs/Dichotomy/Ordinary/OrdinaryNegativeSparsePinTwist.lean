import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparsePinProduct
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMinimalRank
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineRankOne

/-! Exact pin/twist commutation for genuine original-port pinning. All pinned
phase factors are retained as one explicit nonzero scalar; no coefficient or
field extension is silently installed as a physical resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparsePinTwist
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeSparseMinimalRank
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n m : ℕ}


def pinScalar (p : Fin n→Bool ⊕ Fin m) : AlgebraicComplex :=
  fixedProduct p (fun b=>if b then zetaEight else 1)

theorem pinScalar_nonzero (p : Fin n→Bool ⊕ Fin m) : pinScalar p≠0 := by
  unfold pinScalar fixedProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  cases b <;> simp [zetaEight_ne_zero]

/-- Uniform eighth-root twist commutes with a real original-port pinning
up to exactly the phase contributed by the pinned original coordinates. -/
theorem uniform_pin (f : Signature AlgebraicComplex n) (p : Fin n→Bool ⊕ Fin m)
    (hp : PurePins p) :
    (fun x=>OrdinaryNegativeAffineRankOne.uniform f (T.substitute p x))=
      fun x=>pinScalar p*OrdinaryNegativeAffineRankOne.uniform (fun y=>f (T.substitute p y)) x := by
  funext x
  simp only [OrdinaryNegativeAffineRankOne.uniform,localTwist_apply,Bool.true_and]
  rw [product_pure p hp (fun b=>if b then zetaEight else 1) x]
  exact mul_assoc _ _ _

/-- Nonzero pinned phase scalars do not change the literal Affine class. -/
theorem uniform_pin_affine_iff (f : Signature AlgebraicComplex n)
    (p : Fin n→Bool ⊕ Fin m) (hp : PurePins p) :
    Affine (fun x=>OrdinaryNegativeAffineRankOne.uniform f (T.substitute p x)) ↔
      Affine (OrdinaryNegativeAffineRankOne.uniform (fun y=>f (T.substitute p y))) := by
  rw [uniform_pin f p hp]
  constructor
  · intro h
    convert h.scale (pinScalar p)⁻¹ using 1
    funext x
    rw [←mul_assoc,inv_mul_cancel₀ (pinScalar_nonzero p),one_mul]
  · intro h
    exact h.scale (pinScalar p)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparsePinTwist
end
