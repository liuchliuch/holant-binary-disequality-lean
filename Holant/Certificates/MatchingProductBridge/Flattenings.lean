import Holant.Certificates.MatchingProductBridge.Tensors
import Holant.Certificates.MatchingProductBridge.SwapRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The three literal binary flattenings, with their actual matrix ranks. -/
namespace Holant.Certificates.MatchingProductBridge
open Matrix
open scoped Kronecker
noncomputable section

abbrev PairMatrix := Matrix (Bool × Bool) (Bool × Bool) ℂ

def flatten0 (W : FourTensor) : PairMatrix := fun i j => W ![i.1,i.2,j.1,j.2]
def flatten1 (W : FourTensor) : PairMatrix := fun i j => W ![i.1,j.1,i.2,j.2]
def flatten2 (W : FourTensor) : PairMatrix := fun i j => W ![i.1,j.1,j.2,i.2]

def matchingTensor (r : Fin 3) (U V : Matrix Bool Bool ℂ) : FourTensor :=
  if r = 0 then P0 U V else if r = 1 then P1 U V else P2 U V

def flatten (r : Fin 3) (W : FourTensor) : PairMatrix :=
  if r = 0 then flatten0 W else if r = 1 then flatten1 W else flatten2 W

@[simp] theorem flatten_add (r : Fin 3) (X Y : FourTensor) :
    flatten r (X+Y) = flatten r X + flatten r Y := by
  fin_cases r <;> rfl
@[simp] theorem flatten_sub (r : Fin 3) (X Y : FourTensor) :
    flatten r (X-Y) = flatten r X - flatten r Y := by
  fin_cases r <;> rfl
@[simp] theorem flatten_smul (r : Fin 3) (c : ℂ) (X : FourTensor) :
    flatten r (c • X) = c • flatten r X := by
  fin_cases r <;> rfl
@[simp] theorem flatten_zero (r : Fin 3) : flatten r 0 = 0 := by
  fin_cases r <;> rfl

@[simp] theorem flatten0_P0 (U V : Matrix Bool Bool ℂ) :
    flatten0 (P0 U V) = vecMulVec (fun i => U i.1 i.2) (fun j => V j.1 j.2) := by
  ext i j; simp [flatten0,P0,vecMulVec]
@[simp] theorem flatten0_P1 (U V : Matrix Bool Bool ℂ) : flatten0 (P1 U V) = U ⊗ₖ V := by
  ext i j; simp [flatten0,P1]
@[simp] theorem flatten0_P2 (U V : Matrix Bool Bool ℂ) :
    flatten0 (P2 U V) = (U ⊗ₖ V) * tensorSwap := by
  ext ⟨i₁,i₂⟩ ⟨j₁,j₂⟩
  cases i₁ <;> cases i₂ <;> cases j₁ <;> cases j₂ <;>
    simp [flatten0,P2,Matrix.mul_apply,tensorSwap]
@[simp] theorem flatten1_P0 (U V : Matrix Bool Bool ℂ) : flatten1 (P0 U V) = U ⊗ₖ V := by
  ext i j; simp [flatten1,P0]
@[simp] theorem flatten1_P1 (U V : Matrix Bool Bool ℂ) :
    flatten1 (P1 U V) = vecMulVec (fun i => U i.1 i.2) (fun j => V j.1 j.2) := by
  ext i j; simp [flatten1,P1,vecMulVec]
@[simp] theorem flatten1_P2 (U V : Matrix Bool Bool ℂ) :
    flatten1 (P2 U V) = (U ⊗ₖ V.transpose) * tensorSwap := by
  ext ⟨i₁,i₂⟩ ⟨j₁,j₂⟩
  cases i₁ <;> cases i₂ <;> cases j₁ <;> cases j₂ <;>
    simp [flatten1,P2,Matrix.mul_apply,tensorSwap]
@[simp] theorem flatten2_P0 (U V : Matrix Bool Bool ℂ) : flatten2 (P0 U V) = U ⊗ₖ V.transpose := by
  ext i j; simp [flatten2,P0]
@[simp] theorem flatten2_P1 (U V : Matrix Bool Bool ℂ) :
    flatten2 (P1 U V) = (U ⊗ₖ V.transpose) * tensorSwap := by
  ext ⟨i₁,i₂⟩ ⟨j₁,j₂⟩
  cases i₁ <;> cases i₂ <;> cases j₁ <;> cases j₂ <;>
    simp [flatten2,P1,Matrix.mul_apply,tensorSwap]
@[simp] theorem flatten2_P2 (U V : Matrix Bool Bool ℂ) :
    flatten2 (P2 U V) = vecMulVec (fun i => U i.1 i.2) (fun j => V j.1 j.2) := by
  ext i j; simp [flatten2,P2,vecMulVec]

theorem tensorSwap_sq : tensorSwap * tensorSwap = 1 := by
  ext ⟨i₁,i₂⟩ ⟨j₁,j₂⟩
  cases i₁ <;> cases i₂ <;> cases j₁ <;> cases j₂ <;>
    simp [Matrix.mul_apply,tensorSwap]

theorem rank_mul_tensorSwap (M : PairMatrix) : (M * tensorSwap).rank = M.rank := by
  apply le_antisymm (Matrix.rank_mul_le_left _ _)
  have h := Matrix.rank_mul_le_left (M * tensorSwap) tensorSwap
  simpa [Matrix.mul_assoc,tensorSwap_sq] using h

theorem binary_has_nonzero_entry (U : Matrix Bool Bool ℂ) (hU : Matrix.det U ≠ 0) :
    ∃ a b, U a b ≠ 0 := by
  by_contra h
  push_neg at h
  have : U = 0 := by ext a b; exact h a b
  simp [this] at hU

theorem rank_binary_outer (U V : Matrix Bool Bool ℂ) (hU : Matrix.det U ≠ 0)
    (hV : Matrix.det V ≠ 0) :
    (vecMulVec (fun i : Bool × Bool => U i.1 i.2)
      (fun j : Bool × Bool => V j.1 j.2)).rank = 1 := by
  obtain ⟨a,b,hab⟩ := binary_has_nonzero_entry U hU
  obtain ⟨c,d,hcd⟩ := binary_has_nonzero_entry V hV
  apply le_antisymm (Matrix.rank_vecMulVec_le _ _)
  exact one_le_rank_of_entry_ne_zero _ (a,b) (c,d) (mul_ne_zero hab hcd)

theorem rank_binary_kronecker (U V : Matrix Bool Bool ℂ) (hU : Matrix.det U ≠ 0)
    (hV : Matrix.det V ≠ 0) : (U ⊗ₖ V).rank = 4 := by
  have hd : Matrix.det (U ⊗ₖ V) ≠ 0 := by
    rw [Matrix.det_kronecker]
    exact mul_ne_zero (pow_ne_zero _ hU) (pow_ne_zero _ hV)
  simpa using Matrix.rank_of_det_ne_zero hd

/-- Each invertible matching tensor has rank one on its own matching and rank
four on each of the other two matchings. -/
theorem matching_flattening_rank (r s : Fin 3) (U V : Matrix Bool Bool ℂ)
    (hU : Matrix.det U ≠ 0) (hV : Matrix.det V ≠ 0) :
    (flatten r (matchingTensor s U V)).rank = if r = s then 1 else 4 := by
  have hVt : Matrix.det V.transpose ≠ 0 := by simpa using hV
  fin_cases r <;> fin_cases s <;>
    simp [flatten,matchingTensor,rank_binary_outer U V hU hV,
      rank_binary_kronecker U V hU hV,rank_binary_kronecker U V.transpose hU hVt,
      rank_mul_tensorSwap]

/-- Ordinary matrix rank is subadditive. -/
theorem matrix_rank_add_le {m n : Type*} [Fintype m] [Fintype n]
    (X Y : Matrix m n ℂ) : (X+Y).rank ≤ X.rank + Y.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le X.mulVecLin Y.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem matrix_rank_smul_le {m n : Type*} [Fintype m] [Fintype n]
    (c : ℂ) (X : Matrix m n ℂ) : (c • X).rank ≤ X.rank := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (Matrix.rank_smul_of_mem_nonZeroDivisors X
      (mem_nonZeroDivisors_of_ne_zero hc)).le

/-- The source's forbidden `1,1,4` line configuration, with arbitrary scales. -/
theorem no_mixed_matching_line (r s : Fin 3) (hrs : r ≠ s)
    (U V U' V' L N : Matrix Bool Bool ℂ) (hU : Matrix.det U ≠ 0) (hV : Matrix.det V ≠ 0)
    (hU' : Matrix.det U' ≠ 0) (hV' : Matrix.det V' ≠ 0)
    (hL : Matrix.det L ≠ 0) (hN : Matrix.det N ≠ 0) (a b : ℂ) :
    a • matchingTensor r U V + b • matchingTensor r U' V' ≠ matchingTensor s L N := by
  intro he
  have h := congrArg (fun W => (flatten r W).rank) he
  have bound := matrix_rank_add_le (a • flatten r (matchingTensor r U V))
    (b • flatten r (matchingTensor r U' V'))
  have ha := matrix_rank_smul_le a (flatten r (matchingTensor r U V))
  have hb := matrix_rank_smul_le b (flatten r (matchingTensor r U' V'))
  simp only [flatten_add,flatten_smul] at h
  rw [matching_flattening_rank r s L N hL hN, if_neg hrs] at h
  rw [matching_flattening_rank r r U V hU hV, if_pos rfl] at ha
  rw [matching_flattening_rank r r U' V' hU' hV', if_pos rfl] at hb
  omega

end
end Holant.Certificates.MatchingProductBridge
