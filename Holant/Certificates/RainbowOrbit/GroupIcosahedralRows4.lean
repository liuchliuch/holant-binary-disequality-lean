import Holant.Certificates.RainbowOrbit.GroupIcosahedralData
namespace Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem icosahedral_row_48 : ∀ j : Fin 60,
    icosahedralProductScale 48 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 48) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 48 j) (icosahedralRaw (icosahedralProductIndex 48 j)) ∧
    (48 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 48) (icosahedralRaw j)
      (icosahedralSeparation 48 j).1 (icosahedralSeparation 48 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_49 : ∀ j : Fin 60,
    icosahedralProductScale 49 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 49) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 49 j) (icosahedralRaw (icosahedralProductIndex 49 j)) ∧
    (49 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 49) (icosahedralRaw j)
      (icosahedralSeparation 49 j).1 (icosahedralSeparation 49 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_50 : ∀ j : Fin 60,
    icosahedralProductScale 50 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 50) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 50 j) (icosahedralRaw (icosahedralProductIndex 50 j)) ∧
    (50 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 50) (icosahedralRaw j)
      (icosahedralSeparation 50 j).1 (icosahedralSeparation 50 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_51 : ∀ j : Fin 60,
    icosahedralProductScale 51 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 51) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 51 j) (icosahedralRaw (icosahedralProductIndex 51 j)) ∧
    (51 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 51) (icosahedralRaw j)
      (icosahedralSeparation 51 j).1 (icosahedralSeparation 51 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_52 : ∀ j : Fin 60,
    icosahedralProductScale 52 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 52) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 52 j) (icosahedralRaw (icosahedralProductIndex 52 j)) ∧
    (52 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 52) (icosahedralRaw j)
      (icosahedralSeparation 52 j).1 (icosahedralSeparation 52 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_53 : ∀ j : Fin 60,
    icosahedralProductScale 53 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 53) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 53 j) (icosahedralRaw (icosahedralProductIndex 53 j)) ∧
    (53 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 53) (icosahedralRaw j)
      (icosahedralSeparation 53 j).1 (icosahedralSeparation 53 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_54 : ∀ j : Fin 60,
    icosahedralProductScale 54 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 54) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 54 j) (icosahedralRaw (icosahedralProductIndex 54 j)) ∧
    (54 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 54) (icosahedralRaw j)
      (icosahedralSeparation 54 j).1 (icosahedralSeparation 54 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_55 : ∀ j : Fin 60,
    icosahedralProductScale 55 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 55) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 55 j) (icosahedralRaw (icosahedralProductIndex 55 j)) ∧
    (55 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 55) (icosahedralRaw j)
      (icosahedralSeparation 55 j).1 (icosahedralSeparation 55 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_56 : ∀ j : Fin 60,
    icosahedralProductScale 56 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 56) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 56 j) (icosahedralRaw (icosahedralProductIndex 56 j)) ∧
    (56 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 56) (icosahedralRaw j)
      (icosahedralSeparation 56 j).1 (icosahedralSeparation 56 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_57 : ∀ j : Fin 60,
    icosahedralProductScale 57 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 57) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 57 j) (icosahedralRaw (icosahedralProductIndex 57 j)) ∧
    (57 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 57) (icosahedralRaw j)
      (icosahedralSeparation 57 j).1 (icosahedralSeparation 57 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_58 : ∀ j : Fin 60,
    icosahedralProductScale 58 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 58) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 58 j) (icosahedralRaw (icosahedralProductIndex 58 j)) ∧
    (58 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 58) (icosahedralRaw j)
      (icosahedralSeparation 58 j).1 (icosahedralSeparation 58 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_59 : ∀ j : Fin 60,
    icosahedralProductScale 59 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 59) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 59 j) (icosahedralRaw (icosahedralProductIndex 59 j)) ∧
    (59 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 59) (icosahedralRaw j)
      (icosahedralSeparation 59 j).1 (icosahedralSeparation 59 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

end Holant.Certificates.RainbowOrbit
