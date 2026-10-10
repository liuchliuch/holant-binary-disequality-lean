import Holant.Certificates.RainbowOrbit.GroupOctahedralData
namespace Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem octahedral_row_0 : ∀ j : Fin 24,
    octahedralProductScale 0 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 0) (octahedralRaw j) =
      goldenScale (octahedralProductScale 0 j) (octahedralRaw (octahedralProductIndex 0 j)) ∧
    (0 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 0) (octahedralRaw j)
      (octahedralSeparation 0 j).1 (octahedralSeparation 0 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_1 : ∀ j : Fin 24,
    octahedralProductScale 1 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 1) (octahedralRaw j) =
      goldenScale (octahedralProductScale 1 j) (octahedralRaw (octahedralProductIndex 1 j)) ∧
    (1 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 1) (octahedralRaw j)
      (octahedralSeparation 1 j).1 (octahedralSeparation 1 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_2 : ∀ j : Fin 24,
    octahedralProductScale 2 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 2) (octahedralRaw j) =
      goldenScale (octahedralProductScale 2 j) (octahedralRaw (octahedralProductIndex 2 j)) ∧
    (2 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 2) (octahedralRaw j)
      (octahedralSeparation 2 j).1 (octahedralSeparation 2 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_3 : ∀ j : Fin 24,
    octahedralProductScale 3 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 3) (octahedralRaw j) =
      goldenScale (octahedralProductScale 3 j) (octahedralRaw (octahedralProductIndex 3 j)) ∧
    (3 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 3) (octahedralRaw j)
      (octahedralSeparation 3 j).1 (octahedralSeparation 3 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_4 : ∀ j : Fin 24,
    octahedralProductScale 4 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 4) (octahedralRaw j) =
      goldenScale (octahedralProductScale 4 j) (octahedralRaw (octahedralProductIndex 4 j)) ∧
    (4 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 4) (octahedralRaw j)
      (octahedralSeparation 4 j).1 (octahedralSeparation 4 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_5 : ∀ j : Fin 24,
    octahedralProductScale 5 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 5) (octahedralRaw j) =
      goldenScale (octahedralProductScale 5 j) (octahedralRaw (octahedralProductIndex 5 j)) ∧
    (5 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 5) (octahedralRaw j)
      (octahedralSeparation 5 j).1 (octahedralSeparation 5 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_6 : ∀ j : Fin 24,
    octahedralProductScale 6 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 6) (octahedralRaw j) =
      goldenScale (octahedralProductScale 6 j) (octahedralRaw (octahedralProductIndex 6 j)) ∧
    (6 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 6) (octahedralRaw j)
      (octahedralSeparation 6 j).1 (octahedralSeparation 6 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_7 : ∀ j : Fin 24,
    octahedralProductScale 7 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 7) (octahedralRaw j) =
      goldenScale (octahedralProductScale 7 j) (octahedralRaw (octahedralProductIndex 7 j)) ∧
    (7 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 7) (octahedralRaw j)
      (octahedralSeparation 7 j).1 (octahedralSeparation 7 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_8 : ∀ j : Fin 24,
    octahedralProductScale 8 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 8) (octahedralRaw j) =
      goldenScale (octahedralProductScale 8 j) (octahedralRaw (octahedralProductIndex 8 j)) ∧
    (8 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 8) (octahedralRaw j)
      (octahedralSeparation 8 j).1 (octahedralSeparation 8 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_9 : ∀ j : Fin 24,
    octahedralProductScale 9 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 9) (octahedralRaw j) =
      goldenScale (octahedralProductScale 9 j) (octahedralRaw (octahedralProductIndex 9 j)) ∧
    (9 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 9) (octahedralRaw j)
      (octahedralSeparation 9 j).1 (octahedralSeparation 9 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_10 : ∀ j : Fin 24,
    octahedralProductScale 10 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 10) (octahedralRaw j) =
      goldenScale (octahedralProductScale 10 j) (octahedralRaw (octahedralProductIndex 10 j)) ∧
    (10 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 10) (octahedralRaw j)
      (octahedralSeparation 10 j).1 (octahedralSeparation 10 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_11 : ∀ j : Fin 24,
    octahedralProductScale 11 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 11) (octahedralRaw j) =
      goldenScale (octahedralProductScale 11 j) (octahedralRaw (octahedralProductIndex 11 j)) ∧
    (11 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 11) (octahedralRaw j)
      (octahedralSeparation 11 j).1 (octahedralSeparation 11 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

end Holant.Certificates.RainbowOrbit
