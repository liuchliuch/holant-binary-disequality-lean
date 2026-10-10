import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneData
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
theorem quotient_pair_exact_1_0 : ∀j : Fin 24,pairTable 1 0 j=rawPair (rawPoint 1 0) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_1 : ∀j : Fin 24,pairTable 1 1 j=rawPair (rawPoint 1 1) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_2 : ∀j : Fin 24,pairTable 1 2 j=rawPair (rawPoint 1 2) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_3 : ∀j : Fin 24,pairTable 1 3 j=rawPair (rawPoint 1 3) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_4 : ∀j : Fin 24,pairTable 1 4 j=rawPair (rawPoint 1 4) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_5 : ∀j : Fin 24,pairTable 1 5 j=rawPair (rawPoint 1 5) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_6 : ∀j : Fin 24,pairTable 1 6 j=rawPair (rawPoint 1 6) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_7 : ∀j : Fin 24,pairTable 1 7 j=rawPair (rawPoint 1 7) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_8 : ∀j : Fin 24,pairTable 1 8 j=rawPair (rawPoint 1 8) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_9 : ∀j : Fin 24,pairTable 1 9 j=rawPair (rawPoint 1 9) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_10 : ∀j : Fin 24,pairTable 1 10 j=rawPair (rawPoint 1 10) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_11 : ∀j : Fin 24,pairTable 1 11 j=rawPair (rawPoint 1 11) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_12 : ∀j : Fin 24,pairTable 1 12 j=rawPair (rawPoint 1 12) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_13 : ∀j : Fin 24,pairTable 1 13 j=rawPair (rawPoint 1 13) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_14 : ∀j : Fin 24,pairTable 1 14 j=rawPair (rawPoint 1 14) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_15 : ∀j : Fin 24,pairTable 1 15 j=rawPair (rawPoint 1 15) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_16 : ∀j : Fin 24,pairTable 1 16 j=rawPair (rawPoint 1 16) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_17 : ∀j : Fin 24,pairTable 1 17 j=rawPair (rawPoint 1 17) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_18 : ∀j : Fin 24,pairTable 1 18 j=rawPair (rawPoint 1 18) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_19 : ∀j : Fin 24,pairTable 1 19 j=rawPair (rawPoint 1 19) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_20 : ∀j : Fin 24,pairTable 1 20 j=rawPair (rawPoint 1 20) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_21 : ∀j : Fin 24,pairTable 1 21 j=rawPair (rawPoint 1 21) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_22 : ∀j : Fin 24,pairTable 1 22 j=rawPair (rawPoint 1 22) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1_23 : ∀j : Fin 24,pairTable 1 23 j=rawPair (rawPoint 1 23) (rawPoint 1 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_1 (i j : Fin 24) : pairTable 1 i j=rawPair (rawPoint 1 i) (rawPoint 1 j) := by
  fin_cases i
  · exact quotient_pair_exact_1_0 j
  · exact quotient_pair_exact_1_1 j
  · exact quotient_pair_exact_1_2 j
  · exact quotient_pair_exact_1_3 j
  · exact quotient_pair_exact_1_4 j
  · exact quotient_pair_exact_1_5 j
  · exact quotient_pair_exact_1_6 j
  · exact quotient_pair_exact_1_7 j
  · exact quotient_pair_exact_1_8 j
  · exact quotient_pair_exact_1_9 j
  · exact quotient_pair_exact_1_10 j
  · exact quotient_pair_exact_1_11 j
  · exact quotient_pair_exact_1_12 j
  · exact quotient_pair_exact_1_13 j
  · exact quotient_pair_exact_1_14 j
  · exact quotient_pair_exact_1_15 j
  · exact quotient_pair_exact_1_16 j
  · exact quotient_pair_exact_1_17 j
  · exact quotient_pair_exact_1_18 j
  · exact quotient_pair_exact_1_19 j
  · exact quotient_pair_exact_1_20 j
  · exact quotient_pair_exact_1_21 j
  · exact quotient_pair_exact_1_22 j
  · exact quotient_pair_exact_1_23 j
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
