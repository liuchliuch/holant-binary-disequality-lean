import Holant.Certificates.OctahedralSeparator.Data

/-! Candidate product indices and exact scales.  The final theorems check every
one of the 576 products by kernel reduction in the faithful scalar algebra. -/
namespace Holant.Certificates.OctahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

def productIndex : Fin 24 → Fin 24 → Fin 24 :=
  ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],
    ![1,0,3,2,10,8,11,9,5,7,4,6,13,12,21,20,18,19,16,17,15,14,23,22],
    ![2,3,0,1,7,11,8,4,6,10,9,5,22,23,15,14,19,18,17,16,21,20,12,13],
    ![3,2,1,0,9,6,5,10,11,4,7,8,23,22,20,21,17,16,19,18,14,15,13,12],
    ![4,9,10,7,11,1,3,6,2,5,8,0,20,14,18,16,22,12,13,23,17,19,15,21],
    ![5,11,6,8,2,10,4,1,9,3,0,7,18,17,23,12,14,21,15,20,22,13,19,16],
    ![6,8,5,11,1,7,9,2,4,0,3,10,19,16,12,23,20,15,21,14,13,22,18,17],
    ![7,10,9,4,5,3,1,8,0,11,6,2,21,15,17,19,12,22,23,13,18,16,14,20],
    ![8,6,11,5,3,4,10,0,7,2,1,9,16,19,22,13,21,14,20,15,23,12,17,18],
    ![9,4,7,10,8,2,0,5,1,6,11,3,14,20,19,17,13,23,22,12,16,18,21,15],
    ![10,7,4,9,6,0,2,11,3,8,5,1,15,21,16,18,23,13,12,22,19,17,20,14],
    ![11,5,8,6,0,9,7,3,10,1,2,4,17,18,13,22,15,20,14,21,12,23,16,19],
    ![12,13,23,22,18,21,20,19,14,17,16,15,1,0,5,6,4,7,10,9,11,8,2,3],
    ![13,12,22,23,16,14,15,17,21,19,18,20,0,1,8,11,10,9,4,7,6,5,3,2],
    ![14,20,15,21,22,18,16,12,19,23,13,17,4,9,2,0,8,5,11,6,3,1,7,10],
    ![15,21,14,20,12,17,19,22,16,13,23,18,7,10,0,2,6,11,5,8,1,3,4,9],
    ![16,19,18,17,20,12,23,15,22,14,21,13,6,8,4,10,3,0,1,2,9,7,11,5],
    ![17,18,19,16,14,23,12,21,13,20,15,22,5,11,9,7,0,3,2,1,4,10,8,6],
    ![18,17,16,19,15,13,22,20,23,21,14,12,11,5,10,4,2,1,0,3,7,9,6,8],
    ![19,16,17,18,21,22,13,14,12,15,20,23,8,6,7,9,1,2,3,0,10,4,5,11],
    ![20,14,21,15,13,19,17,23,18,12,22,16,9,4,1,3,11,6,8,5,0,2,10,7],
    ![21,15,20,14,23,16,18,13,17,22,12,19,10,7,3,1,5,8,6,11,2,0,9,4],
    ![22,23,13,12,17,20,21,16,15,18,19,14,3,2,11,8,7,4,9,10,5,6,0,1],
    ![23,22,12,13,19,15,14,18,20,16,17,21,2,3,6,5,9,10,7,4,8,11,1,0]]

def productRational : Fin 24 → Fin 24 → ℚ :=
  ![![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
    ![1,(-1),(-1),1,(-1),(-1),(-1),(-1),1,1,1,1,(-1),1,1,1,1,1,(-1),(-1),(-1),(-1),1,(-1)],
    ![1,1,(-1),(-1),(-1),(-1),1,1,(-1),(-1),1,1,1,1,(-1),1,(-1),1,(-1),1,(-1),1,(-1),(-1)],
    ![1,(-1),1,(-1),(-1),1,(-1),1,(-1),1,(-1),1,(-1),1,1,(-1),(-1),1,1,(-1),(-1),1,(-1),1],
    ![1,(-1),(-1),(-1),(-2),4,4,2,4,2,2,4,2,2,2,2,2,2,(-2),(-2),(-2),2,(-2),2],
    ![1,(-1),(-1),1,4,(-2),2,4,2,(-4),4,2,2,2,2,2,2,2,(-2),2,2,(-2),(-2),(-2)],
    ![1,(-1),1,(-1),4,2,(-2),(-4),2,4,4,2,2,2,2,(-2),2,2,2,(-2),(-2),(-2),2,2],
    ![1,(-1),1,1,2,(-4),4,(-2),4,2,2,(-4),2,2,2,2,2,(-2),2,(-2),2,(-2),2,(-2)],
    ![1,1,(-1),(-1),4,2,2,4,(-2),4,(-4),2,2,(-2),2,2,(-2),2,2,2,(-2),2,(-2),2],
    ![1,1,(-1),1,2,4,4,2,(-4),(-2),2,(-4),2,(-2),(-2),2,2,2,2,2,2,2,(-2),(-2)],
    ![1,1,1,(-1),2,4,(-4),2,4,2,(-2),(-4),2,(-2),2,(-2),(-2),2,2,(-2),2,2,2,2],
    ![1,1,1,1,4,2,2,(-4),2,(-4),(-4),(-2),2,(-2),2,(-2),2,(-2),2,2,2,2,2,(-2)],
    ![1,(-1),1,1,2,2,2,2,2,2,2,2,2,2,1,1,1,1,(-1),(-1),(-1),(-1),2,(-2)],
    ![1,1,1,(-1),2,2,2,2,(-2),(-2),(-2),(-2),2,(-2),1,1,1,1,1,1,1,1,2,2],
    ![1,1,(-1),(-1),2,2,2,2,(-2),2,2,2,1,1,2,2,1,1,(-1),1,2,2,(-1),(-1)],
    ![1,1,1,1,2,2,2,(-2),2,2,(-2),(-2),1,1,2,(-2),1,1,1,(-1),2,(-2),1,1],
    ![1,1,1,(-1),2,2,(-2),2,2,2,(-2),2,1,1,1,1,2,2,2,(-2),(-1),1,(-1),1],
    ![1,1,(-1),1,2,2,2,2,2,(-2),2,(-2),1,1,1,1,2,(-2),2,2,1,(-1),1,(-1)],
    ![1,(-1),(-1),(-1),(-2),(-2),2,2,2,2,2,2,(-1),1,(-1),1,2,2,(-2),2,(-1),(-1),(-1),(-1)],
    ![1,(-1),1,1,2,(-2),(-2),(-2),2,2,2,(-2),(-1),1,1,(-1),2,(-2),(-2),(-2),(-1),(-1),1,1],
    ![1,(-1),1,(-1),(-2),2,(-2),(-2),2,2,2,2,(-1),1,2,2,(-1),1,(-1),(-1),(-2),(-2),(-1),1],
    ![1,(-1),(-1),1,2,(-2),2,(-2),2,(-2),2,2,(-1),1,(-2),2,1,(-1),(-1),(-1),2,(-2),1,(-1)],
    ![1,(-1),(-1),(-1),(-2),2,(-2),2,(-2),2,(-2),2,2,2,(-1),1,(-1),1,(-1),1,(-1),1,(-2),2],
    ![1,1,(-1),1,(-2),(-2),2,2,(-2),(-2),2,2,2,(-2),(-1),1,1,(-1),(-1),1,1,(-1),(-2),(-2)]]

def productScale (i j : Fin 24) : Scalar := rat (productRational i j)

theorem productScale_nonzero_0 : ∀ j : Fin 24, productScale 0 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_0 : ∀ j : Fin 24,
    mm (standard 0) (standard j) = ms (productScale 0 j) (standard (productIndex 0 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_1 : ∀ j : Fin 24, productScale 1 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_1 : ∀ j : Fin 24,
    mm (standard 1) (standard j) = ms (productScale 1 j) (standard (productIndex 1 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_2 : ∀ j : Fin 24, productScale 2 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_2 : ∀ j : Fin 24,
    mm (standard 2) (standard j) = ms (productScale 2 j) (standard (productIndex 2 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_3 : ∀ j : Fin 24, productScale 3 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_3 : ∀ j : Fin 24,
    mm (standard 3) (standard j) = ms (productScale 3 j) (standard (productIndex 3 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_4 : ∀ j : Fin 24, productScale 4 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_4 : ∀ j : Fin 24,
    mm (standard 4) (standard j) = ms (productScale 4 j) (standard (productIndex 4 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_5 : ∀ j : Fin 24, productScale 5 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_5 : ∀ j : Fin 24,
    mm (standard 5) (standard j) = ms (productScale 5 j) (standard (productIndex 5 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_6 : ∀ j : Fin 24, productScale 6 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_6 : ∀ j : Fin 24,
    mm (standard 6) (standard j) = ms (productScale 6 j) (standard (productIndex 6 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_7 : ∀ j : Fin 24, productScale 7 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_7 : ∀ j : Fin 24,
    mm (standard 7) (standard j) = ms (productScale 7 j) (standard (productIndex 7 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_8 : ∀ j : Fin 24, productScale 8 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_8 : ∀ j : Fin 24,
    mm (standard 8) (standard j) = ms (productScale 8 j) (standard (productIndex 8 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_9 : ∀ j : Fin 24, productScale 9 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_9 : ∀ j : Fin 24,
    mm (standard 9) (standard j) = ms (productScale 9 j) (standard (productIndex 9 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_10 : ∀ j : Fin 24, productScale 10 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_10 : ∀ j : Fin 24,
    mm (standard 10) (standard j) = ms (productScale 10 j) (standard (productIndex 10 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_11 : ∀ j : Fin 24, productScale 11 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_11 : ∀ j : Fin 24,
    mm (standard 11) (standard j) = ms (productScale 11 j) (standard (productIndex 11 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_12 : ∀ j : Fin 24, productScale 12 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_12 : ∀ j : Fin 24,
    mm (standard 12) (standard j) = ms (productScale 12 j) (standard (productIndex 12 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_13 : ∀ j : Fin 24, productScale 13 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_13 : ∀ j : Fin 24,
    mm (standard 13) (standard j) = ms (productScale 13 j) (standard (productIndex 13 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_14 : ∀ j : Fin 24, productScale 14 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_14 : ∀ j : Fin 24,
    mm (standard 14) (standard j) = ms (productScale 14 j) (standard (productIndex 14 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_15 : ∀ j : Fin 24, productScale 15 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_15 : ∀ j : Fin 24,
    mm (standard 15) (standard j) = ms (productScale 15 j) (standard (productIndex 15 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_16 : ∀ j : Fin 24, productScale 16 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_16 : ∀ j : Fin 24,
    mm (standard 16) (standard j) = ms (productScale 16 j) (standard (productIndex 16 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_17 : ∀ j : Fin 24, productScale 17 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_17 : ∀ j : Fin 24,
    mm (standard 17) (standard j) = ms (productScale 17 j) (standard (productIndex 17 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_18 : ∀ j : Fin 24, productScale 18 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_18 : ∀ j : Fin 24,
    mm (standard 18) (standard j) = ms (productScale 18 j) (standard (productIndex 18 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_19 : ∀ j : Fin 24, productScale 19 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_19 : ∀ j : Fin 24,
    mm (standard 19) (standard j) = ms (productScale 19 j) (standard (productIndex 19 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_20 : ∀ j : Fin 24, productScale 20 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_20 : ∀ j : Fin 24,
    mm (standard 20) (standard j) = ms (productScale 20 j) (standard (productIndex 20 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_21 : ∀ j : Fin 24, productScale 21 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_21 : ∀ j : Fin 24,
    mm (standard 21) (standard j) = ms (productScale 21 j) (standard (productIndex 21 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_22 : ∀ j : Fin 24, productScale 22 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_22 : ∀ j : Fin 24,
    mm (standard 22) (standard j) = ms (productScale 22 j) (standard (productIndex 22 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero_23 : ∀ j : Fin 24, productScale 23 j ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

theorem standard_product_23 : ∀ j : Fin 24,
    mm (standard 23) (standard j) = ms (productScale 23 j) (standard (productIndex 23 j)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem productScale_nonzero : ∀ i j : Fin 24, productScale i j ≠ 0 := by
  intro i
  fin_cases i
  · exact productScale_nonzero_0
  · exact productScale_nonzero_1
  · exact productScale_nonzero_2
  · exact productScale_nonzero_3
  · exact productScale_nonzero_4
  · exact productScale_nonzero_5
  · exact productScale_nonzero_6
  · exact productScale_nonzero_7
  · exact productScale_nonzero_8
  · exact productScale_nonzero_9
  · exact productScale_nonzero_10
  · exact productScale_nonzero_11
  · exact productScale_nonzero_12
  · exact productScale_nonzero_13
  · exact productScale_nonzero_14
  · exact productScale_nonzero_15
  · exact productScale_nonzero_16
  · exact productScale_nonzero_17
  · exact productScale_nonzero_18
  · exact productScale_nonzero_19
  · exact productScale_nonzero_20
  · exact productScale_nonzero_21
  · exact productScale_nonzero_22
  · exact productScale_nonzero_23

theorem standard_product : ∀ i j : Fin 24,
    mm (standard i) (standard j) = ms (productScale i j) (standard (productIndex i j)) := by
  intro i
  fin_cases i
  · exact standard_product_0
  · exact standard_product_1
  · exact standard_product_2
  · exact standard_product_3
  · exact standard_product_4
  · exact standard_product_5
  · exact standard_product_6
  · exact standard_product_7
  · exact standard_product_8
  · exact standard_product_9
  · exact standard_product_10
  · exact standard_product_11
  · exact standard_product_12
  · exact standard_product_13
  · exact standard_product_14
  · exact standard_product_15
  · exact standard_product_16
  · exact standard_product_17
  · exact standard_product_18
  · exact standard_product_19
  · exact standard_product_20
  · exact standard_product_21
  · exact standard_product_22
  · exact standard_product_23

end Holant.Certificates.OctahedralSeparator
