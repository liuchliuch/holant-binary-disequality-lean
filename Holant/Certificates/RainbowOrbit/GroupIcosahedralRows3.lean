import Holant.Certificates.RainbowOrbit.GroupIcosahedralData
namespace Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem icosahedral_row_36 : ∀ j : Fin 60,
    icosahedralProductScale 36 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 36) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 36 j) (icosahedralRaw (icosahedralProductIndex 36 j)) ∧
    (36 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 36) (icosahedralRaw j)
      (icosahedralSeparation 36 j).1 (icosahedralSeparation 36 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_37 : ∀ j : Fin 60,
    icosahedralProductScale 37 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 37) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 37 j) (icosahedralRaw (icosahedralProductIndex 37 j)) ∧
    (37 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 37) (icosahedralRaw j)
      (icosahedralSeparation 37 j).1 (icosahedralSeparation 37 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_38 : ∀ j : Fin 60,
    icosahedralProductScale 38 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 38) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 38 j) (icosahedralRaw (icosahedralProductIndex 38 j)) ∧
    (38 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 38) (icosahedralRaw j)
      (icosahedralSeparation 38 j).1 (icosahedralSeparation 38 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_39 : ∀ j : Fin 60,
    icosahedralProductScale 39 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 39) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 39 j) (icosahedralRaw (icosahedralProductIndex 39 j)) ∧
    (39 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 39) (icosahedralRaw j)
      (icosahedralSeparation 39 j).1 (icosahedralSeparation 39 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_40 : ∀ j : Fin 60,
    icosahedralProductScale 40 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 40) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 40 j) (icosahedralRaw (icosahedralProductIndex 40 j)) ∧
    (40 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 40) (icosahedralRaw j)
      (icosahedralSeparation 40 j).1 (icosahedralSeparation 40 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_41 : ∀ j : Fin 60,
    icosahedralProductScale 41 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 41) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 41 j) (icosahedralRaw (icosahedralProductIndex 41 j)) ∧
    (41 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 41) (icosahedralRaw j)
      (icosahedralSeparation 41 j).1 (icosahedralSeparation 41 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_42 : ∀ j : Fin 60,
    icosahedralProductScale 42 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 42) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 42 j) (icosahedralRaw (icosahedralProductIndex 42 j)) ∧
    (42 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 42) (icosahedralRaw j)
      (icosahedralSeparation 42 j).1 (icosahedralSeparation 42 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_43 : ∀ j : Fin 60,
    icosahedralProductScale 43 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 43) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 43 j) (icosahedralRaw (icosahedralProductIndex 43 j)) ∧
    (43 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 43) (icosahedralRaw j)
      (icosahedralSeparation 43 j).1 (icosahedralSeparation 43 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_44 : ∀ j : Fin 60,
    icosahedralProductScale 44 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 44) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 44 j) (icosahedralRaw (icosahedralProductIndex 44 j)) ∧
    (44 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 44) (icosahedralRaw j)
      (icosahedralSeparation 44 j).1 (icosahedralSeparation 44 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_45 : ∀ j : Fin 60,
    icosahedralProductScale 45 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 45) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 45 j) (icosahedralRaw (icosahedralProductIndex 45 j)) ∧
    (45 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 45) (icosahedralRaw j)
      (icosahedralSeparation 45 j).1 (icosahedralSeparation 45 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_46 : ∀ j : Fin 60,
    icosahedralProductScale 46 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 46) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 46 j) (icosahedralRaw (icosahedralProductIndex 46 j)) ∧
    (46 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 46) (icosahedralRaw j)
      (icosahedralSeparation 46 j).1 (icosahedralSeparation 46 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

theorem icosahedral_row_47 : ∀ j : Fin 60,
    icosahedralProductScale 47 j ≠ 0 ∧
    goldenQuaternionProduct (icosahedralRaw 47) (icosahedralRaw j) =
      goldenScale (icosahedralProductScale 47 j) (icosahedralRaw (icosahedralProductIndex 47 j)) ∧
    (47 ≠ j → GoldenInt.norm (goldenCross (icosahedralRaw 47) (icosahedralRaw j)
      (icosahedralSeparation 47 j).1 (icosahedralSeparation 47 j).2) ≠ 0) := by
  intro j
  fin_cases j <;> decide +kernel

end Holant.Certificates.RainbowOrbit
