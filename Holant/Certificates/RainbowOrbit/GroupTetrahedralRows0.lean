import Holant.Certificates.RainbowOrbit.GroupTetrahedralData
namespace Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem tetrahedral_row_0 : ∀ j : Fin 12,
    tetrahedralProductScale 0 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 0) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 0 j) (tetrahedralRaw (tetrahedralProductIndex 0 j)) ∧
    (0 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 0) (tetrahedralRaw j)
      (tetrahedralSeparation 0 j).1 (tetrahedralSeparation 0 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem tetrahedral_row_1 : ∀ j : Fin 12,
    tetrahedralProductScale 1 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 1) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 1 j) (tetrahedralRaw (tetrahedralProductIndex 1 j)) ∧
    (1 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 1) (tetrahedralRaw j)
      (tetrahedralSeparation 1 j).1 (tetrahedralSeparation 1 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem tetrahedral_row_2 : ∀ j : Fin 12,
    tetrahedralProductScale 2 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 2) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 2 j) (tetrahedralRaw (tetrahedralProductIndex 2 j)) ∧
    (2 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 2) (tetrahedralRaw j)
      (tetrahedralSeparation 2 j).1 (tetrahedralSeparation 2 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem tetrahedral_row_3 : ∀ j : Fin 12,
    tetrahedralProductScale 3 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 3) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 3 j) (tetrahedralRaw (tetrahedralProductIndex 3 j)) ∧
    (3 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 3) (tetrahedralRaw j)
      (tetrahedralSeparation 3 j).1 (tetrahedralSeparation 3 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem tetrahedral_row_4 : ∀ j : Fin 12,
    tetrahedralProductScale 4 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 4) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 4 j) (tetrahedralRaw (tetrahedralProductIndex 4 j)) ∧
    (4 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 4) (tetrahedralRaw j)
      (tetrahedralSeparation 4 j).1 (tetrahedralSeparation 4 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem tetrahedral_row_5 : ∀ j : Fin 12,
    tetrahedralProductScale 5 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 5) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 5 j) (tetrahedralRaw (tetrahedralProductIndex 5 j)) ∧
    (5 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 5) (tetrahedralRaw j)
      (tetrahedralSeparation 5 j).1 (tetrahedralSeparation 5 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem tetrahedral_row_6 : ∀ j : Fin 12,
    tetrahedralProductScale 6 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 6) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 6 j) (tetrahedralRaw (tetrahedralProductIndex 6 j)) ∧
    (6 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 6) (tetrahedralRaw j)
      (tetrahedralSeparation 6 j).1 (tetrahedralSeparation 6 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem tetrahedral_row_7 : ∀ j : Fin 12,
    tetrahedralProductScale 7 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 7) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 7 j) (tetrahedralRaw (tetrahedralProductIndex 7 j)) ∧
    (7 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 7) (tetrahedralRaw j)
      (tetrahedralSeparation 7 j).1 (tetrahedralSeparation 7 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem tetrahedral_row_8 : ∀ j : Fin 12,
    tetrahedralProductScale 8 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 8) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 8 j) (tetrahedralRaw (tetrahedralProductIndex 8 j)) ∧
    (8 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 8) (tetrahedralRaw j)
      (tetrahedralSeparation 8 j).1 (tetrahedralSeparation 8 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem tetrahedral_row_9 : ∀ j : Fin 12,
    tetrahedralProductScale 9 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 9) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 9 j) (tetrahedralRaw (tetrahedralProductIndex 9 j)) ∧
    (9 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 9) (tetrahedralRaw j)
      (tetrahedralSeparation 9 j).1 (tetrahedralSeparation 9 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem tetrahedral_row_10 : ∀ j : Fin 12,
    tetrahedralProductScale 10 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 10) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 10 j) (tetrahedralRaw (tetrahedralProductIndex 10 j)) ∧
    (10 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 10) (tetrahedralRaw j)
      (tetrahedralSeparation 10 j).1 (tetrahedralSeparation 10 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem tetrahedral_row_11 : ∀ j : Fin 12,
    tetrahedralProductScale 11 j ≠ 0 ∧
    goldenQuaternionProduct (tetrahedralRaw 11) (tetrahedralRaw j) =
      goldenScale (tetrahedralProductScale 11 j) (tetrahedralRaw (tetrahedralProductIndex 11 j)) ∧
    (11 ≠ j → GoldenInt.norm (goldenCross (tetrahedralRaw 11) (tetrahedralRaw j)
      (tetrahedralSeparation 11 j).1 (tetrahedralSeparation 11 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

end Holant.Certificates.RainbowOrbit
