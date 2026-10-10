import Holant.Certificates.RainbowOrbit.GroupIcosahedralData
namespace Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem icosahedral_row_0 : ∀ j : Fin 60,
    icosahedralProductScale 0 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 0) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 0 j) (icosahedralRaw (icosahedralProductIndex 0 j)) ∧
    (0 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 0) (icosahedralRaw j)
      (icosahedralSeparation 0 j).1 (icosahedralSeparation 0 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_1 : ∀ j : Fin 60,
    icosahedralProductScale 1 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 1) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 1 j) (icosahedralRaw (icosahedralProductIndex 1 j)) ∧
    (1 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 1) (icosahedralRaw j)
      (icosahedralSeparation 1 j).1 (icosahedralSeparation 1 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_2 : ∀ j : Fin 60,
    icosahedralProductScale 2 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 2) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 2 j) (icosahedralRaw (icosahedralProductIndex 2 j)) ∧
    (2 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 2) (icosahedralRaw j)
      (icosahedralSeparation 2 j).1 (icosahedralSeparation 2 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_3 : ∀ j : Fin 60,
    icosahedralProductScale 3 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 3) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 3 j) (icosahedralRaw (icosahedralProductIndex 3 j)) ∧
    (3 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 3) (icosahedralRaw j)
      (icosahedralSeparation 3 j).1 (icosahedralSeparation 3 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_4 : ∀ j : Fin 60,
    icosahedralProductScale 4 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 4) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 4 j) (icosahedralRaw (icosahedralProductIndex 4 j)) ∧
    (4 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 4) (icosahedralRaw j)
      (icosahedralSeparation 4 j).1 (icosahedralSeparation 4 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_5 : ∀ j : Fin 60,
    icosahedralProductScale 5 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 5) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 5 j) (icosahedralRaw (icosahedralProductIndex 5 j)) ∧
    (5 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 5) (icosahedralRaw j)
      (icosahedralSeparation 5 j).1 (icosahedralSeparation 5 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_6 : ∀ j : Fin 60,
    icosahedralProductScale 6 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 6) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 6 j) (icosahedralRaw (icosahedralProductIndex 6 j)) ∧
    (6 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 6) (icosahedralRaw j)
      (icosahedralSeparation 6 j).1 (icosahedralSeparation 6 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_7 : ∀ j : Fin 60,
    icosahedralProductScale 7 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 7) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 7 j) (icosahedralRaw (icosahedralProductIndex 7 j)) ∧
    (7 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 7) (icosahedralRaw j)
      (icosahedralSeparation 7 j).1 (icosahedralSeparation 7 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_8 : ∀ j : Fin 60,
    icosahedralProductScale 8 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 8) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 8 j) (icosahedralRaw (icosahedralProductIndex 8 j)) ∧
    (8 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 8) (icosahedralRaw j)
      (icosahedralSeparation 8 j).1 (icosahedralSeparation 8 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_9 : ∀ j : Fin 60,
    icosahedralProductScale 9 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 9) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 9 j) (icosahedralRaw (icosahedralProductIndex 9 j)) ∧
    (9 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 9) (icosahedralRaw j)
      (icosahedralSeparation 9 j).1 (icosahedralSeparation 9 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_10 : ∀ j : Fin 60,
    icosahedralProductScale 10 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 10) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 10 j) (icosahedralRaw (icosahedralProductIndex 10 j)) ∧
    (10 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 10) (icosahedralRaw j)
      (icosahedralSeparation 10 j).1 (icosahedralSeparation 10 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_11 : ∀ j : Fin 60,
    icosahedralProductScale 11 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 11) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 11 j) (icosahedralRaw (icosahedralProductIndex 11 j)) ∧
    (11 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 11) (icosahedralRaw j)
      (icosahedralSeparation 11 j).1 (icosahedralSeparation 11 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

end Holant.Certificates.RainbowOrbit
