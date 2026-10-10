import Holant.Certificates.IcosahedralSeparator.Maps
import Holant.Certificates.IcosahedralSeparator.UniformDeterminants
import Holant.Certificates.TetrahedralBridge.Counts

/-! Actual matrix ranks of all thirty-six normalized complex-linear maps. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

def cardMatrix (i : Fin 36) : Matrix (Fin 16) (Fin 4) ℂ := fun row k =>
  sourceMap i (quaternionBasis k) (TetrahedralDeck.words row)

theorem low_map_eq (i : Fin 6) : sourceMap (i.castAdd 30) = TetrahedralBridge.sourceMap (i.castAdd 6) := by
  apply TetrahedralBridge.map_ext_basis
  intro k
  rw [sourceMap_basis,TetrahedralBridge.sourceMap_basis]
  fin_cases i <;> fin_cases k <;> rfl

theorem low_rank_two (i : Fin 6) : (cardMatrix (i.castAdd 30)).rank = 2 := by
  have he : cardMatrix (i.castAdd 30) = TetrahedralBridge.cardMatrix (i.castAdd 6) := by
    ext row k
    simp only [cardMatrix,TetrahedralBridge.cardMatrix,low_map_eq]
  rw [he]
  exact TetrahedralBridge.low_rank_two i

def q2code (a b : Bool) : ℤ := if a = b then 0 else if a then -1 else 1
def highCardCode (i : Fin 30) (row : Fin 16) : Fin 4 → GScalar :=
  let x := TetrahedralDeck.words row
  ![gint (4*q2code (x 0) (x 3)*q2code (x 1) (x 2)),
    candidateTable ((ordering i 0).natAdd 3) row,
    candidateTable ((ordering i 1).natAdd 3) row,
    candidateTable ((ordering i 2).natAdd 3) row]

def highRows (i : Fin 30) : Fin 4 → Fin 16 := if i.val < 6 then ![0,3,5,6] else ![0,1,2,3]

theorem highCardCode_minor_nonzero : ∀ i : Fin 30,
    gdet4 (fun r c => highCardCode i (highRows i r) c) ≠ gz := by decide +kernel

theorem gembed_highCardCode (i : Fin 30) (row : Fin 16) (k : Fin 4) :
    gembed (highCardCode i row k) = 8*cardMatrix (i.natAdd 6) row k := by
  fin_cases k
  · fin_cases row <;>
      norm_num [highCardCode,q2code,cardMatrix,sourceMap_basis,sourceImages,
        TetrahedralDeck.words,C,P2,Q2,smul_eq_mul]
  · simp [highCardCode,cardMatrix,sourceMap_basis,sourceImages,high_orderedTuple,
      candidateTable_correct,gembed_candidateCode,candidate]
  · simp [highCardCode,cardMatrix,sourceMap_basis,sourceImages,high_orderedTuple,
      candidateTable_correct,gembed_candidateCode,candidate]
  · simp [highCardCode,cardMatrix,sourceMap_basis,sourceImages,high_orderedTuple,
      candidateTable_correct,gembed_candidateCode,candidate]

theorem high_minor_nonzero (i : Fin 30) :
    Matrix.det ((cardMatrix (i.natAdd 6)).submatrix (highRows i) id) ≠ 0 := by
  have hn := gembed_ne_zero (highCardCode_minor_nonzero i)
  rw [gembed_gdet4] at hn
  have he : (fun r c => gembed (highCardCode i (highRows i r) c)) =
      (8 : ℂ) • ((cardMatrix (i.natAdd 6)).submatrix (highRows i) id) := by
    ext r c
    exact gembed_highCardCode i _ _
  rw [he,Matrix.det_smul] at hn
  intro hz
  exact hn (by rw [hz,mul_zero])

theorem high_rank_four (i : Fin 30) : (cardMatrix (i.natAdd 6)).rank = 4 := by
  have hl := Matrix.rank_submatrix_le (cardMatrix (i.natAdd 6)) (highRows i) id
  have hr := Matrix.rank_of_det_ne_zero (high_minor_nonzero i)
  norm_num at hr
  rw [hr] at hl
  have hu := Matrix.rank_le_card_width (cardMatrix (i.natAdd 6))
  norm_num at hu
  omega

end
end Holant.Certificates.IcosahedralSeparator
