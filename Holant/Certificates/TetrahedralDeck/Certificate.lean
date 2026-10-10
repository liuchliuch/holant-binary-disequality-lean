import Holant.Certificates.TetrahedralDeck.Checks0
import Holant.Certificates.TetrahedralDeck.Checks1
import Holant.Certificates.TetrahedralDeck.Checks2

/-! Complete kernel-checked coverage of the three times fifteen times twelve
actual survivor cases; all finite matrix entries and pivot guards are checked. -/
namespace Holant.Certificates.TetrahedralDeck
set_option maxRecDepth 100000

theorem checked_all (s : Fin 3) (p : Fin 15) (k : Fin 12) : Valid s p k (certificate s p k) := by
  fin_cases s <;> fin_cases p
  · exact checked_0_0 k
  · exact checked_0_1 k
  · exact checked_0_2 k
  · exact checked_0_3 k
  · exact checked_0_4 k
  · exact checked_0_5 k
  · exact checked_0_6 k
  · exact checked_0_7 k
  · exact checked_0_8 k
  · exact checked_0_9 k
  · exact checked_0_10 k
  · exact checked_0_11 k
  · exact checked_0_12 k
  · exact checked_0_13 k
  · exact checked_0_14 k
  · exact checked_1_0 k
  · exact checked_1_1 k
  · exact checked_1_2 k
  · exact checked_1_3 k
  · exact checked_1_4 k
  · exact checked_1_5 k
  · exact checked_1_6 k
  · exact checked_1_7 k
  · exact checked_1_8 k
  · exact checked_1_9 k
  · exact checked_1_10 k
  · exact checked_1_11 k
  · exact checked_1_12 k
  · exact checked_1_13 k
  · exact checked_1_14 k
  · exact checked_2_0 k
  · exact checked_2_1 k
  · exact checked_2_2 k
  · exact checked_2_3 k
  · exact checked_2_4 k
  · exact checked_2_5 k
  · exact checked_2_6 k
  · exact checked_2_7 k
  · exact checked_2_8 k
  · exact checked_2_9 k
  · exact checked_2_10 k
  · exact checked_2_11 k
  · exact checked_2_12 k
  · exact checked_2_13 k
  · exact checked_2_14 k

theorem case_count : Fintype.card (Fin 3 × Fin 15 × Fin 12) = 540 := by decide

end Holant.Certificates.TetrahedralDeck
