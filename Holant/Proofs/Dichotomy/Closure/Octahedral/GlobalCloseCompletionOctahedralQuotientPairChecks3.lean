import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneData
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
theorem quotient_pair_exact_3_0 : ∀j : Fin 24,pairTable 3 0 j=rawPair (rawPoint 3 0) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_1 : ∀j : Fin 24,pairTable 3 1 j=rawPair (rawPoint 3 1) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_2 : ∀j : Fin 24,pairTable 3 2 j=rawPair (rawPoint 3 2) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_3 : ∀j : Fin 24,pairTable 3 3 j=rawPair (rawPoint 3 3) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_4 : ∀j : Fin 24,pairTable 3 4 j=rawPair (rawPoint 3 4) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_5 : ∀j : Fin 24,pairTable 3 5 j=rawPair (rawPoint 3 5) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_6 : ∀j : Fin 24,pairTable 3 6 j=rawPair (rawPoint 3 6) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_7 : ∀j : Fin 24,pairTable 3 7 j=rawPair (rawPoint 3 7) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_8 : ∀j : Fin 24,pairTable 3 8 j=rawPair (rawPoint 3 8) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_9 : ∀j : Fin 24,pairTable 3 9 j=rawPair (rawPoint 3 9) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_10 : ∀j : Fin 24,pairTable 3 10 j=rawPair (rawPoint 3 10) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_11 : ∀j : Fin 24,pairTable 3 11 j=rawPair (rawPoint 3 11) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_12 : ∀j : Fin 24,pairTable 3 12 j=rawPair (rawPoint 3 12) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_13 : ∀j : Fin 24,pairTable 3 13 j=rawPair (rawPoint 3 13) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_14 : ∀j : Fin 24,pairTable 3 14 j=rawPair (rawPoint 3 14) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_15 : ∀j : Fin 24,pairTable 3 15 j=rawPair (rawPoint 3 15) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_16 : ∀j : Fin 24,pairTable 3 16 j=rawPair (rawPoint 3 16) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_17 : ∀j : Fin 24,pairTable 3 17 j=rawPair (rawPoint 3 17) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_18 : ∀j : Fin 24,pairTable 3 18 j=rawPair (rawPoint 3 18) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_19 : ∀j : Fin 24,pairTable 3 19 j=rawPair (rawPoint 3 19) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_20 : ∀j : Fin 24,pairTable 3 20 j=rawPair (rawPoint 3 20) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_21 : ∀j : Fin 24,pairTable 3 21 j=rawPair (rawPoint 3 21) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_22 : ∀j : Fin 24,pairTable 3 22 j=rawPair (rawPoint 3 22) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3_23 : ∀j : Fin 24,pairTable 3 23 j=rawPair (rawPoint 3 23) (rawPoint 3 j) := by
  intro j
  fin_cases j <;> decide +kernel
theorem quotient_pair_exact_3 (i j : Fin 24) : pairTable 3 i j=rawPair (rawPoint 3 i) (rawPoint 3 j) := by
  fin_cases i
  · exact quotient_pair_exact_3_0 j
  · exact quotient_pair_exact_3_1 j
  · exact quotient_pair_exact_3_2 j
  · exact quotient_pair_exact_3_3 j
  · exact quotient_pair_exact_3_4 j
  · exact quotient_pair_exact_3_5 j
  · exact quotient_pair_exact_3_6 j
  · exact quotient_pair_exact_3_7 j
  · exact quotient_pair_exact_3_8 j
  · exact quotient_pair_exact_3_9 j
  · exact quotient_pair_exact_3_10 j
  · exact quotient_pair_exact_3_11 j
  · exact quotient_pair_exact_3_12 j
  · exact quotient_pair_exact_3_13 j
  · exact quotient_pair_exact_3_14 j
  · exact quotient_pair_exact_3_15 j
  · exact quotient_pair_exact_3_16 j
  · exact quotient_pair_exact_3_17 j
  · exact quotient_pair_exact_3_18 j
  · exact quotient_pair_exact_3_19 j
  · exact quotient_pair_exact_3_20 j
  · exact quotient_pair_exact_3_21 j
  · exact quotient_pair_exact_3_22 j
  · exact quotient_pair_exact_3_23 j
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
