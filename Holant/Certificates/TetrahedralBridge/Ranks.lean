import Holant.Certificates.TetrahedralBridge.Maps
import Holant.Certificates.TetrahedralDeck.AllSix

/-! True matrix ranks of the twelve actual coefficient maps: six rank2 maps
and six rank4 maps, with explicit factorizations and nonzero minors. -/
namespace Holant.Certificates.TetrahedralBridge
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def cardMatrix (i : Fin 12) : Matrix (Fin 16) (Fin 4) ℂ := fun row k =>
  sourceMap i (quaternionBasis k) (TetrahedralDeck.words row)

def lowLeft : Matrix (Fin 16) Bool ℂ := fun row b =>
  if b then (1/2 : ℂ)*B (TetrahedralDeck.words row) else (1/2 : ℂ)*A (TetrahedralDeck.words row)
def lowRight (i : Fin 6) : Matrix Bool (Fin 4) ℂ := fun b k =>
  let coeff : Fin 3 → ℂ := fun j => if ordered (i.castAdd 6) j = (if b then (2 : Fin 6) else 1) then 1 else 0
  ![(if b then -1 else 1),coeff 0,coeff 1,coeff 2] k

theorem low_factorization (i : Fin 6) : cardMatrix (i.castAdd 6) = lowLeft*lowRight i := by
  fin_cases i <;> ext row k <;> fin_cases k <;>
    norm_num [cardMatrix,sourceMap_basis,sourceImages,orderedTuple,ordered,candidate,
      lowLeft,lowRight,Matrix.mul_apply,smul_eq_mul,← A_sub_B] <;> ring

def lowRows : Fin 2 → Fin 16 := ![0,3]
def aColumn : Fin 6 → Fin 4 := ![2,1,3,3,1,2]
def lowCols (i : Fin 6) : Fin 2 → Fin 4 := ![0,aColumn i]

theorem low_minor_nonzero (i : Fin 6) :
    Matrix.det ((cardMatrix (i.castAdd 6)).submatrix lowRows (lowCols i)) ≠ 0 := by
  fin_cases i <;>
    norm_num [Matrix.det_fin_two,Matrix.submatrix_apply,lowRows,lowCols,aColumn,
      cardMatrix,sourceMap_basis,sourceImages,orderedTuple,ordered,candidate,
      TetrahedralDeck.words,A,B,C,P0,P1,P2,Q0,Q2,Signature.equality,smul_eq_mul]

theorem low_rank_two (i : Fin 6) : (cardMatrix (i.castAdd 6)).rank = 2 := by
  have hu : (cardMatrix (i.castAdd 6)).rank ≤ 2 := by
    rw [low_factorization]
    exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width lowLeft)
  have hl := Matrix.rank_submatrix_le (cardMatrix (i.castAdd 6)) lowRows (lowCols i)
  have hr := Matrix.rank_of_det_ne_zero (low_minor_nonzero i)
  norm_num at hr
  rw [hr] at hl
  omega

theorem high_matrix (i : Fin 6) : cardMatrix (i.natAdd 6) = TetrahedralDeck.basisCardMatrix i := by
  ext row k
  change sourceMap (i.natAdd 6) (quaternionBasis k) (TetrahedralDeck.words row) =
    Signature.contract (quaternionBasis k) (TetrahedralDeck.allAncestor i) (TetrahedralDeck.words row)
  rw [sourceMap_basis,TetrahedralDeck.basis_recovered]
  fin_cases i <;> fin_cases k <;> rfl

theorem high_rank_four (i : Fin 6) : (cardMatrix (i.natAdd 6)).rank = 4 := by
  rw [high_matrix]
  exact TetrahedralDeck.basis_card_rank_four i

end
end Holant.Certificates.TetrahedralBridge
