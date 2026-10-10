import Holant.Certificates.RainbowOrbit.GroupOctahedralData
namespace Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem octahedral_row_12 : ∀ j : Fin 24,
    octahedralProductScale 12 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 12) (octahedralRaw j) =
      goldenScale (octahedralProductScale 12 j) (octahedralRaw (octahedralProductIndex 12 j)) ∧
    (12 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 12) (octahedralRaw j)
      (octahedralSeparation 12 j).1 (octahedralSeparation 12 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_13 : ∀ j : Fin 24,
    octahedralProductScale 13 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 13) (octahedralRaw j) =
      goldenScale (octahedralProductScale 13 j) (octahedralRaw (octahedralProductIndex 13 j)) ∧
    (13 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 13) (octahedralRaw j)
      (octahedralSeparation 13 j).1 (octahedralSeparation 13 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_14 : ∀ j : Fin 24,
    octahedralProductScale 14 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 14) (octahedralRaw j) =
      goldenScale (octahedralProductScale 14 j) (octahedralRaw (octahedralProductIndex 14 j)) ∧
    (14 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 14) (octahedralRaw j)
      (octahedralSeparation 14 j).1 (octahedralSeparation 14 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_15 : ∀ j : Fin 24,
    octahedralProductScale 15 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 15) (octahedralRaw j) =
      goldenScale (octahedralProductScale 15 j) (octahedralRaw (octahedralProductIndex 15 j)) ∧
    (15 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 15) (octahedralRaw j)
      (octahedralSeparation 15 j).1 (octahedralSeparation 15 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_16 : ∀ j : Fin 24,
    octahedralProductScale 16 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 16) (octahedralRaw j) =
      goldenScale (octahedralProductScale 16 j) (octahedralRaw (octahedralProductIndex 16 j)) ∧
    (16 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 16) (octahedralRaw j)
      (octahedralSeparation 16 j).1 (octahedralSeparation 16 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_17 : ∀ j : Fin 24,
    octahedralProductScale 17 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 17) (octahedralRaw j) =
      goldenScale (octahedralProductScale 17 j) (octahedralRaw (octahedralProductIndex 17 j)) ∧
    (17 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 17) (octahedralRaw j)
      (octahedralSeparation 17 j).1 (octahedralSeparation 17 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_18 : ∀ j : Fin 24,
    octahedralProductScale 18 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 18) (octahedralRaw j) =
      goldenScale (octahedralProductScale 18 j) (octahedralRaw (octahedralProductIndex 18 j)) ∧
    (18 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 18) (octahedralRaw j)
      (octahedralSeparation 18 j).1 (octahedralSeparation 18 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_19 : ∀ j : Fin 24,
    octahedralProductScale 19 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 19) (octahedralRaw j) =
      goldenScale (octahedralProductScale 19 j) (octahedralRaw (octahedralProductIndex 19 j)) ∧
    (19 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 19) (octahedralRaw j)
      (octahedralSeparation 19 j).1 (octahedralSeparation 19 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_20 : ∀ j : Fin 24,
    octahedralProductScale 20 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 20) (octahedralRaw j) =
      goldenScale (octahedralProductScale 20 j) (octahedralRaw (octahedralProductIndex 20 j)) ∧
    (20 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 20) (octahedralRaw j)
      (octahedralSeparation 20 j).1 (octahedralSeparation 20 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_21 : ∀ j : Fin 24,
    octahedralProductScale 21 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 21) (octahedralRaw j) =
      goldenScale (octahedralProductScale 21 j) (octahedralRaw (octahedralProductIndex 21 j)) ∧
    (21 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 21) (octahedralRaw j)
      (octahedralSeparation 21 j).1 (octahedralSeparation 21 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_22 : ∀ j : Fin 24,
    octahedralProductScale 22 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 22) (octahedralRaw j) =
      goldenScale (octahedralProductScale 22 j) (octahedralRaw (octahedralProductIndex 22 j)) ∧
    (22 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 22) (octahedralRaw j)
      (octahedralSeparation 22 j).1 (octahedralSeparation 22 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem octahedral_row_23 : ∀ j : Fin 24,
    octahedralProductScale 23 j ≠ 0 ∧
    goldenQuaternionProduct (octahedralRaw 23) (octahedralRaw j) =
      goldenScale (octahedralProductScale 23 j) (octahedralRaw (octahedralProductIndex 23 j)) ∧
    (23 ≠ j → GoldenInt.norm (goldenCross (octahedralRaw 23) (octahedralRaw j)
      (octahedralSeparation 23 j).1 (octahedralSeparation 23 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

end Holant.Certificates.RainbowOrbit
