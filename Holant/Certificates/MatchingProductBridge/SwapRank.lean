import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

namespace Holant.Certificates.MatchingProductBridge

open Matrix
open scoped Kronecker

/-- The swap operator on two binary factors. -/
def tensorSwap : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun i j => if i = (j.2, j.1) then 1 else 0

/-- The defined matrix has the stated action on binary tensor coordinates. -/
@[simp] theorem tensorSwap_mulVec (v : Bool × Bool → ℂ) (i : Bool × Bool) :
    (tensorSwap *ᵥ v) i = v (i.2, i.1) := by
  rcases i with ⟨i₁,i₂⟩
  cases i₁ <;> cases i₂ <;>
    simp [Matrix.mulVec, dotProduct, tensorSwap, Fintype.sum_prod_type]

/-- The rank-tested operator in the matching-product bridge. -/
def swapDifference (U V : Matrix Bool Bool ℂ) (lam : ℂ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (U ⊗ₖ V.transpose) * tensorSwap - lam • 1

@[simp] theorem swapDifference_apply (U V : Matrix Bool Bool ℂ) (lam : ℂ)
    (i j : Bool × Bool) :
    swapDifference U V lam i j = U i.1 j.2 * V j.1 i.2 -
      lam * (if i = j then 1 else 0) := by
  rcases i with ⟨i₁,i₂⟩
  rcases j with ⟨j₁,j₂⟩
  cases i₁ <;> cases i₂ <;> cases j₁ <;> cases j₂ <;>
    simp [swapDifference, Matrix.mul_apply, tensorSwap]

/-- Every two by two minor of a matrix of rank at most one vanishes. -/
theorem minor_two_eq_zero_of_rank_le_one {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) (hM : M.rank ≤ 1) (i k : m) (j l : n) :
    M i j * M k l - M i l * M k j = 0 := by
  let r : Fin 2 → m := ![i,k]
  let c : Fin 2 → n := ![j,l]
  have hminor := M.rank_submatrix_le r c
  have hd : (M.submatrix r c).det = 0 := by
    by_contra hn
    have hr := Matrix.rank_of_det_ne_zero hn
    simp only [Fintype.card_fin] at hr
    omega
  simpa [Matrix.det_fin_two, Matrix.submatrix, r, c] using hd

/-- A nonzero entry gives the lower rank bound needed for rank one. -/
theorem one_le_rank_of_entry_ne_zero {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) (i : m) (j : n) (h : M i j ≠ 0) : 1 ≤ M.rank := by
  let r : Fin 1 → m := fun _ => i
  let c : Fin 1 → n := fun _ => j
  have hn : (M.submatrix r c).det ≠ 0 := by simpa [Matrix.det_fin_one, r, c] using h
  have hr := Matrix.rank_of_det_ne_zero hn
  have hm := M.rank_submatrix_le r c
  simpa only [hr, Fintype.card_fin] using hm

/-- The exact rank criterion after the manuscript's conjugation reduction. -/
theorem reduced_swap_rank_one_iff (W : Matrix Bool Bool ℂ) (lam : ℂ) (hlam : lam ≠ 0) :
    (swapDifference 1 W lam).rank = 1 ↔ W = lam • 1 := by
  constructor
  · intro hr
    have minor := minor_two_eq_zero_of_rank_le_one (swapDifference 1 W lam) hr.le
    have ha := minor (false,false) (false,true) (false,false) (false,true)
    have hc := minor (false,false) (false,true) (false,true) (true,false)
    have hb := minor (false,true) (true,false) (false,false) (false,true)
    have hd := minor (false,true) (true,false) (false,true) (true,false)
    simp at ha hc hb hd
    have ha' : W false false = lam := by
      exact sub_eq_zero.mp (ha.resolve_right hlam)
    have hc' : W true false = 0 := hc.resolve_right hlam
    have hb' : W false true = 0 := by
      rw [ha'] at hb
      exact hb.resolve_right hlam
    have hd' : W true true = lam := by
      rw [ha'] at hd
      have : lam * (W true true - lam) = 0 := by linear_combination -hd
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hlam)
    ext i j
    cases i <;> cases j <;> simp [ha', hb', hc', hd']
  · intro hW
    subst W
    let v : Bool × Bool → ℂ := fun i =>
      if i = (false,true) then 1 else if i = (true,false) then -1 else 0
    have he : swapDifference 1 (lam • 1) lam = Matrix.vecMulVec (fun i => -lam * v i) v := by
      ext ⟨i₁,i₂⟩ ⟨j₁,j₂⟩
      cases i₁ <;> cases i₂ <;> cases j₁ <;> cases j₂ <;>
        simp [v, Matrix.vecMulVec]
    apply le_antisymm
    · rw [he]
      exact Matrix.rank_vecMulVec_le _ _
    · apply one_le_rank_of_entry_ne_zero _ (false,true) (false,true)
      simpa [Matrix.one_apply] using neg_ne_zero.mpr hlam


/-- Swapping the factors intertwines the two Kronecker actions. -/
theorem tensorSwap_mul_kronecker (U V : Matrix Bool Bool ℂ) :
    tensorSwap * (U ⊗ₖ V) = (V ⊗ₖ U) * tensorSwap := by
  ext ⟨i₁,i₂⟩ ⟨j₁,j₂⟩
  cases i₁ <;> cases i₂ <;> cases j₁ <;> cases j₂ <;>
    simp [Matrix.mul_apply, tensorSwap, mul_comm, Fintype.sum_prod_type]

/-- Conjugation by an invertible matrix preserves the actual matrix rank. -/
theorem rank_conjugate_of_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (L R M : Matrix n n ℂ) (hRL : R * L = 1) :
    (L * M * R).rank = M.rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have he : M = R * (L * M * R) * L := by
      simp only [Matrix.mul_assoc, hRL, Matrix.mul_one]
      rw [← Matrix.mul_assoc, hRL, Matrix.one_mul]
    calc M.rank = (R * (L * M * R) * L).rank := congrArg Matrix.rank he
      _ ≤ (R * (L * M * R)).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (L * M * R).rank := Matrix.rank_mul_le_right _ _

/-- The manuscript's conjugation reduction, as an equality of matrices. -/
theorem conjugate_swapDifference (U V : Matrix Bool Bool ℂ) (lam : ℂ)
    (hU : IsUnit U.det) :
    (U⁻¹ ⊗ₖ (1 : Matrix Bool Bool ℂ)) * swapDifference U V lam *
      (U ⊗ₖ (1 : Matrix Bool Bool ℂ)) =
      swapDifference 1 (U.transpose * V) lam := by
  have hleft : (U⁻¹ ⊗ₖ (1 : Matrix Bool Bool ℂ)) * (U ⊗ₖ V.transpose) =
      (1 : Matrix Bool Bool ℂ) ⊗ₖ V.transpose := by
    rw [← Matrix.mul_kronecker_mul, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
  have hunit : (U⁻¹ ⊗ₖ (1 : Matrix Bool Bool ℂ)) * (U ⊗ₖ (1 : Matrix Bool Bool ℂ)) = 1 := by
    rw [← Matrix.mul_kronecker_mul, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul,
      Matrix.one_kronecker_one]
  calc
    _ = ((U⁻¹ ⊗ₖ (1 : Matrix Bool Bool ℂ)) * (U ⊗ₖ V.transpose)) *
        (tensorSwap * (U ⊗ₖ (1 : Matrix Bool Bool ℂ))) -
        lam • ((U⁻¹ ⊗ₖ (1 : Matrix Bool Bool ℂ)) * (U ⊗ₖ (1 : Matrix Bool Bool ℂ))) := by
      simp [swapDifference, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = ((1 : Matrix Bool Bool ℂ) ⊗ₖ V.transpose) *
        (((1 : Matrix Bool Bool ℂ) ⊗ₖ U) * tensorSwap) - lam • 1 := by
      rw [hleft, tensorSwap_mul_kronecker, hunit]
    _ = swapDifference 1 (U.transpose * V) lam := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
      simp [swapDifference, Matrix.transpose_mul]

/-- The first assertion of the matching-product bridge lemma.  In fact, only
invertibility of `U` is needed: the conclusion supplies invertibility of `V`. -/
theorem swap_rank_one_iff (U V : Matrix Bool Bool ℂ) (lam : ℂ)
    (hU : IsUnit U.det) (hlam : lam ≠ 0) :
    (swapDifference U V lam).rank = 1 ↔ V = lam • U⁻¹.transpose := by
  have hunit : (U ⊗ₖ (1 : Matrix Bool Bool ℂ)) * (U⁻¹ ⊗ₖ (1 : Matrix Bool Bool ℂ)) = 1 := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul,
      Matrix.one_kronecker_one]
  have hr := rank_conjugate_of_inverse (U⁻¹ ⊗ₖ (1 : Matrix Bool Bool ℂ))
    (U ⊗ₖ (1 : Matrix Bool Bool ℂ)) (swapDifference U V lam) hunit
  rw [conjugate_swapDifference U V lam hU] at hr
  rw [← hr, reduced_swap_rank_one_iff _ _ hlam]
  constructor
  · intro h
    have ht : U⁻¹.transpose * U.transpose = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hU, Matrix.transpose_one]
    calc
      V = U⁻¹.transpose * (U.transpose * V) := by rw [← Matrix.mul_assoc, ht, Matrix.one_mul]
      _ = lam • U⁻¹.transpose := by rw [h, Matrix.mul_smul, Matrix.mul_one]
  · intro h
    rw [h, Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hU,
      Matrix.transpose_one]


/-- The literal source formula, using a nonzero determinant hypothesis. -/
theorem kronecker_swap_rank_one_iff (U V : Matrix Bool Bool ℂ) (lam : ℂ)
    (hU : U.det ≠ 0) (hlam : lam ≠ 0) :
    ((U ⊗ₖ V.transpose) * tensorSwap - lam • 1).rank = 1 ↔
      V = lam • U⁻¹.transpose :=
  swap_rank_one_iff U V lam (isUnit_iff_ne_zero.mpr hU) hlam

/-- The rank-one operator used in the converse of the source argument. -/
theorem tensorSwap_sub_one_rank : (tensorSwap - 1).rank = 1 := by
  have h := (reduced_swap_rank_one_iff (1 : Matrix Bool Bool ℂ) 1 one_ne_zero).mpr (by simp)
  simpa [swapDifference, Matrix.one_kronecker_one] using h

/-- The binary pair order used by the displayed four by four source matrix. -/
def swapPairOrder : Fin 4 → Bool × Bool :=
  ![(false,false), (false,true), (true,false), (true,true)]

/-- Exact correspondence with the displayed reduced matrix in Lemma A.15. -/
theorem reduced_swap_display (W : Matrix Bool Bool ℂ) (lam : ℂ) :
    (swapDifference 1 W lam).submatrix swapPairOrder swapPairOrder =
      !![W false false - lam, 0, W true false, 0;
         W false true, -lam, W true true, 0;
         0, W false false, -lam, W true false;
         0, W false true, 0, W true true - lam] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix, swapPairOrder, Matrix.one_apply]

end Holant.Certificates.MatchingProductBridge
