import Holant.Certificates.RainbowOrbit.GroupIcosahedralData
namespace Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem icosahedral_row_12 : ∀ j : Fin 60,
    icosahedralProductScale 12 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 12) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 12 j) (icosahedralRaw (icosahedralProductIndex 12 j)) ∧
    (12 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 12) (icosahedralRaw j)
      (icosahedralSeparation 12 j).1 (icosahedralSeparation 12 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_13 : ∀ j : Fin 60,
    icosahedralProductScale 13 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 13) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 13 j) (icosahedralRaw (icosahedralProductIndex 13 j)) ∧
    (13 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 13) (icosahedralRaw j)
      (icosahedralSeparation 13 j).1 (icosahedralSeparation 13 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_14 : ∀ j : Fin 60,
    icosahedralProductScale 14 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 14) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 14 j) (icosahedralRaw (icosahedralProductIndex 14 j)) ∧
    (14 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 14) (icosahedralRaw j)
      (icosahedralSeparation 14 j).1 (icosahedralSeparation 14 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_15 : ∀ j : Fin 60,
    icosahedralProductScale 15 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 15) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 15 j) (icosahedralRaw (icosahedralProductIndex 15 j)) ∧
    (15 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 15) (icosahedralRaw j)
      (icosahedralSeparation 15 j).1 (icosahedralSeparation 15 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_16 : ∀ j : Fin 60,
    icosahedralProductScale 16 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 16) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 16 j) (icosahedralRaw (icosahedralProductIndex 16 j)) ∧
    (16 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 16) (icosahedralRaw j)
      (icosahedralSeparation 16 j).1 (icosahedralSeparation 16 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_17 : ∀ j : Fin 60,
    icosahedralProductScale 17 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 17) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 17 j) (icosahedralRaw (icosahedralProductIndex 17 j)) ∧
    (17 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 17) (icosahedralRaw j)
      (icosahedralSeparation 17 j).1 (icosahedralSeparation 17 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_18 : ∀ j : Fin 60,
    icosahedralProductScale 18 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 18) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 18 j) (icosahedralRaw (icosahedralProductIndex 18 j)) ∧
    (18 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 18) (icosahedralRaw j)
      (icosahedralSeparation 18 j).1 (icosahedralSeparation 18 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_19 : ∀ j : Fin 60,
    icosahedralProductScale 19 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 19) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 19 j) (icosahedralRaw (icosahedralProductIndex 19 j)) ∧
    (19 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 19) (icosahedralRaw j)
      (icosahedralSeparation 19 j).1 (icosahedralSeparation 19 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_20 : ∀ j : Fin 60,
    icosahedralProductScale 20 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 20) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 20 j) (icosahedralRaw (icosahedralProductIndex 20 j)) ∧
    (20 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 20) (icosahedralRaw j)
      (icosahedralSeparation 20 j).1 (icosahedralSeparation 20 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_21 : ∀ j : Fin 60,
    icosahedralProductScale 21 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 21) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 21 j) (icosahedralRaw (icosahedralProductIndex 21 j)) ∧
    (21 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 21) (icosahedralRaw j)
      (icosahedralSeparation 21 j).1 (icosahedralSeparation 21 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_22 : ∀ j : Fin 60,
    icosahedralProductScale 22 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 22) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 22 j) (icosahedralRaw (icosahedralProductIndex 22 j)) ∧
    (22 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 22) (icosahedralRaw j)
      (icosahedralSeparation 22 j).1 (icosahedralSeparation 22 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_23 : ∀ j : Fin 60,
    icosahedralProductScale 23 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 23) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 23 j) (icosahedralRaw (icosahedralProductIndex 23 j)) ∧
    (23 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 23) (icosahedralRaw j)
      (icosahedralSeparation 23 j).1 (icosahedralSeparation 23 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

end Holant.Certificates.RainbowOrbit
