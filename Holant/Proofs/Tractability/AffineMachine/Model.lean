import Holant.Proofs.Tractability.AffineMachine.Reconstruction
import Holant.Proofs.Tractability.ProductElimination


namespace Holant.LocalDrafts.Tractability.AffineMachine

open Holant.Tractable AffinePhase TwoTranslate
open scoped BigOperators

structure State (n : ℕ) where
  scale : AlgebraicComplex
  support : AffineSystem n
  phase : QuadraticPhase n

noncomputable def State.value {n : ℕ} (A : State n) (x : Word n) : AlgebraicComplex :=
  affineFormula A.scale A.support A.phase x

noncomputable def State.partition {n : ℕ} (A : State n) : AlgebraicComplex := ∑ x, A.value x

def permute {n : ℕ} (j : Fin (n + 1)) (x : Word (n + 1)) : Word (n + 1) :=
  fun i => x (Equiv.swap 0 j i)

def permutationEquiv {n : ℕ} (j : Fin (n + 1)) : Word (n + 1) ≃ Word (n + 1) where
  toFun := permute j
  invFun := permute j
  left_inv x := by funext i; simp [permute]
  right_inv x := by funext i; simp [permute]

theorem sum_split {n : ℕ} (f : Word (n + 1) → AlgebraicComplex) :
    ∑ x, f x = ∑ x : Word n, (f (Fin.cons false x) + f (Fin.cons true x)) := by
  rw [← (ProductElimination.headTail n).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [ProductElimination.headTail, Equiv.coe_fn_symm_mk, Finset.sum_add_distrib]
  ac_rfl

theorem sum_permuted_split {n : ℕ} (f : Word (n + 1) → AlgebraicComplex) (j : Fin (n + 1)) :
    ∑ x, f x = ∑ x : Word n,
      (f (permute j (Fin.cons false x)) + f (permute j (Fin.cons true x))) := by
  rw [← (permutationEquiv j).sum_comp f]
  exact sum_split (fun x => f (permute j x))

end Holant.LocalDrafts.Tractability.AffineMachine
