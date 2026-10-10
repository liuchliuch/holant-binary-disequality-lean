import Holant.Certificates.RainbowOrbit.GroupIcosahedralData
namespace Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem icosahedral_row_24 : ∀ j : Fin 60,
    icosahedralProductScale 24 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 24) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 24 j) (icosahedralRaw (icosahedralProductIndex 24 j)) ∧
    (24 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 24) (icosahedralRaw j)
      (icosahedralSeparation 24 j).1 (icosahedralSeparation 24 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_25 : ∀ j : Fin 60,
    icosahedralProductScale 25 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 25) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 25 j) (icosahedralRaw (icosahedralProductIndex 25 j)) ∧
    (25 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 25) (icosahedralRaw j)
      (icosahedralSeparation 25 j).1 (icosahedralSeparation 25 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_26 : ∀ j : Fin 60,
    icosahedralProductScale 26 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 26) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 26 j) (icosahedralRaw (icosahedralProductIndex 26 j)) ∧
    (26 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 26) (icosahedralRaw j)
      (icosahedralSeparation 26 j).1 (icosahedralSeparation 26 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_27 : ∀ j : Fin 60,
    icosahedralProductScale 27 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 27) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 27 j) (icosahedralRaw (icosahedralProductIndex 27 j)) ∧
    (27 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 27) (icosahedralRaw j)
      (icosahedralSeparation 27 j).1 (icosahedralSeparation 27 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_28 : ∀ j : Fin 60,
    icosahedralProductScale 28 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 28) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 28 j) (icosahedralRaw (icosahedralProductIndex 28 j)) ∧
    (28 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 28) (icosahedralRaw j)
      (icosahedralSeparation 28 j).1 (icosahedralSeparation 28 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_29 : ∀ j : Fin 60,
    icosahedralProductScale 29 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 29) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 29 j) (icosahedralRaw (icosahedralProductIndex 29 j)) ∧
    (29 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 29) (icosahedralRaw j)
      (icosahedralSeparation 29 j).1 (icosahedralSeparation 29 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_30 : ∀ j : Fin 60,
    icosahedralProductScale 30 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 30) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 30 j) (icosahedralRaw (icosahedralProductIndex 30 j)) ∧
    (30 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 30) (icosahedralRaw j)
      (icosahedralSeparation 30 j).1 (icosahedralSeparation 30 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_31 : ∀ j : Fin 60,
    icosahedralProductScale 31 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 31) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 31 j) (icosahedralRaw (icosahedralProductIndex 31 j)) ∧
    (31 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 31) (icosahedralRaw j)
      (icosahedralSeparation 31 j).1 (icosahedralSeparation 31 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_32 : ∀ j : Fin 60,
    icosahedralProductScale 32 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 32) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 32 j) (icosahedralRaw (icosahedralProductIndex 32 j)) ∧
    (32 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 32) (icosahedralRaw j)
      (icosahedralSeparation 32 j).1 (icosahedralSeparation 32 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_33 : ∀ j : Fin 60,
    icosahedralProductScale 33 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 33) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 33 j) (icosahedralRaw (icosahedralProductIndex 33 j)) ∧
    (33 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 33) (icosahedralRaw j)
      (icosahedralSeparation 33 j).1 (icosahedralSeparation 33 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_34 : ∀ j : Fin 60,
    icosahedralProductScale 34 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 34) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 34 j) (icosahedralRaw (icosahedralProductIndex 34 j)) ∧
    (34 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 34) (icosahedralRaw j)
      (icosahedralSeparation 34 j).1 (icosahedralSeparation 34 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_35 : ∀ j : Fin 60,
    icosahedralProductScale 35 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 35) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 35 j) (icosahedralRaw (icosahedralProductIndex 35 j)) ∧
    (35 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 35) (icosahedralRaw j)
      (icosahedralSeparation 35 j).1 (icosahedralSeparation 35 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

end Holant.Certificates.RainbowOrbit
