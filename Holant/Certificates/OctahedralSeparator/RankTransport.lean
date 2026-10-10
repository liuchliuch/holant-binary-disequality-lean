import Holant.Certificates.MatchingProductBridge.Flattenings
import Holant.Certificates.TetrahedralOrientation.Data
import Holant.BoundaryAction

/-! Nonuniform four-leg coordinate action preserves each of the three actual
flattening ranks.  The proof factors each flattening by its two Kronecker legs. -/
namespace Holant.Certificates.OctahedralSeparator
open Holant
open Holant.Certificates.MatchingProductBridge
open scoped Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Matching0 partitions the four ordered ports as (0,1)|(2,3). -/
theorem flatten0_coordinateAction (L : Fin 4 → Matrix Bool Bool ℂ) (W : FourTensor) :
    flatten0 (Signature.coordinateAction L W) =
      (L 0 ⊗ₖ L 1) * flatten0 W * (L 2 ⊗ₖ L 3).transpose := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [flatten0,Signature.coordinateAction,TetrahedralOrientation.sum_four,
    Fin.prod_univ_succ,Matrix.mul_apply,Fintype.sum_prod_type,
    Finset.mul_sum,Finset.sum_mul]
  ring

/-- Matching1 partitions the four ordered ports as (0,2)|(1,3). -/
theorem flatten1_coordinateAction (L : Fin 4 → Matrix Bool Bool ℂ) (W : FourTensor) :
    flatten1 (Signature.coordinateAction L W) =
      (L 0 ⊗ₖ L 2) * flatten1 W * (L 1 ⊗ₖ L 3).transpose := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [flatten1,Signature.coordinateAction,TetrahedralOrientation.sum_four,
    Fin.prod_univ_succ,Matrix.mul_apply,Fintype.sum_prod_type,
    Finset.mul_sum,Finset.sum_mul]
  ring

/-- Matching2 partitions the four ordered ports as (0,3)|(1,2). -/
theorem flatten2_coordinateAction (L : Fin 4 → Matrix Bool Bool ℂ) (W : FourTensor) :
    flatten2 (Signature.coordinateAction L W) =
      (L 0 ⊗ₖ L 3) * flatten2 W * (L 1 ⊗ₖ L 2).transpose := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [flatten2,Signature.coordinateAction,TetrahedralOrientation.sum_four,
    Fin.prod_univ_succ,Matrix.mul_apply,Fintype.sum_prod_type,
    Finset.mul_sum,Finset.sum_mul]
  ring

theorem kronecker_det_ne_zero (U V : Matrix Bool Bool ℂ)
    (hU : Matrix.det U ≠ 0) (hV : Matrix.det V ≠ 0) :
    Matrix.det (U ⊗ₖ V) ≠ 0 := by
  rw [Matrix.det_kronecker]
  exact mul_ne_zero (pow_ne_zero _ hU) (pow_ne_zero _ hV)

theorem rank_kronecker_dressing (U V A B : Matrix Bool Bool ℂ) (W : PairMatrix)
    (hU : Matrix.det U ≠ 0) (hV : Matrix.det V ≠ 0)
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0) :
    ((U ⊗ₖ V) * W * (A ⊗ₖ B).transpose).rank = W.rank := by
  rw [Matrix.rank_mul_eq_left_of_det_ne_zero _ _
    (by simpa using kronecker_det_ne_zero A B hA hB)]
  exact Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (kronecker_det_ne_zero U V hU hV)

/-- Each actual flattening rank, not only nonsingularity or an upper bound, is invariant. -/
theorem flatten_rank_coordinateAction (L : Fin 4 → Matrix Bool Bool ℂ) (W : FourTensor)
    (hL : ∀ j, Matrix.det (L j) ≠ 0) (r : Fin 3) :
    (flatten r (Signature.coordinateAction L W)).rank = (flatten r W).rank := by
  fin_cases r
  · change (flatten0 (Signature.coordinateAction L W)).rank = (flatten0 W).rank
    rw [flatten0_coordinateAction]
    exact rank_kronecker_dressing _ _ _ _ _ (hL 0) (hL 1) (hL 2) (hL 3)
  · change (flatten1 (Signature.coordinateAction L W)).rank = (flatten1 W).rank
    rw [flatten1_coordinateAction]
    exact rank_kronecker_dressing _ _ _ _ _ (hL 0) (hL 2) (hL 1) (hL 3)
  · change (flatten2 (Signature.coordinateAction L W)).rank = (flatten2 W).rank
    rw [flatten2_coordinateAction]
    exact rank_kronecker_dressing _ _ _ _ _ (hL 0) (hL 3) (hL 1) (hL 2)

/-- A reusable rank profile is transported uniformly over all three matchings. -/
theorem flatten_rank_profile_coordinateAction (L : Fin 4 → Matrix Bool Bool ℂ) (W : FourTensor)
    (hL : ∀ j, Matrix.det (L j) ≠ 0) (profile : Fin 3 → ℕ)
    (hW : ∀ r, (flatten r W).rank = profile r) :
    ∀ r, (flatten r (Signature.coordinateAction L W)).rank = profile r := by
  intro r
  rw [flatten_rank_coordinateAction L W hL r,hW r]

end
end Holant.Certificates.OctahedralSeparator
