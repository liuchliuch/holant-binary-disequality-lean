import Holant.Pauli.ExoticKlein.SixPortCachedIntegerProblem
import Holant.Pauli.ExoticKlein.SixPortAnchorWitness
import Holant.Pauli.ExoticKlein.SixPortIntegerBatches.Batch101
import Holant.Pauli.ExoticKlein.SixPortIntegerBatches.Batch102

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open IntegerCertificate
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

theorem anchorEntry0944_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 944))) := by
  have he : anchorRepresentative 944 = 1623 := by decide +kernel
  rw [he]
  exact irep1623_representative

theorem anchorEntry0945_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 945))) := by
  have he : anchorRepresentative 945 = 1624 := by decide +kernel
  rw [he]
  exact irep1624_representative

theorem anchorEntry0946_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 946))) := by
  have he : anchorRepresentative 946 = 1625 := by decide +kernel
  rw [he]
  exact irep1625_representative

theorem anchorEntry0947_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 947))) := by
  have he : anchorRepresentative 947 = 1626 := by decide +kernel
  rw [he]
  exact irep1626_representative

theorem anchorEntry0948_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 948))) := by
  have he : anchorRepresentative 948 = 1627 := by decide +kernel
  rw [he]
  exact irep1627_representative

theorem anchorEntry0949_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 949))) := by
  have he : anchorRepresentative 949 = 1631 := by decide +kernel
  rw [he]
  exact irep1631_representative

theorem anchorEntry0950_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 950))) := by
  have he : anchorRepresentative 950 = 1632 := by decide +kernel
  rw [he]
  exact irep1632_representative

theorem anchorEntry0951_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 951))) := by
  have he : anchorRepresentative 951 = 1634 := by decide +kernel
  rw [he]
  exact irep1634_representative

theorem anchorEntry0952_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 952))) := by
  have he : anchorRepresentative 952 = 1635 := by decide +kernel
  rw [he]
  exact irep1635_representative

theorem anchorEntry0953_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 953))) := by
  have he : anchorRepresentative 953 = 1636 := by decide +kernel
  rw [he]
  exact irep1636_representative

theorem anchorEntry0954_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 954))) := by
  have he : anchorRepresentative 954 = 1637 := by decide +kernel
  rw [he]
  exact irep1637_representative

theorem anchorEntry0955_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 955))) := by
  have he : anchorRepresentative 955 = 1638 := by decide +kernel
  rw [he]
  exact irep1638_representative

theorem anchorEntry0956_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 956))) := by
  have he : anchorRepresentative 956 = 1639 := by decide +kernel
  rw [he]
  exact irep1639_representative

theorem anchorEntry0957_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 957))) := by
  have he : anchorRepresentative 957 = 1640 := by decide +kernel
  rw [he]
  exact irep1640_representative

theorem anchorEntry0958_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 958))) := by
  have he : anchorRepresentative 958 = 1641 := by decide +kernel
  rw [he]
  exact irep1641_representative

theorem anchorEntry0959_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 959))) := by
  have he : anchorRepresentative 959 = 1642 := by decide +kernel
  rw [he]
  exact irep1642_representative

theorem anchorBatch059 (i : Fin 16) :
    Solved (stateEquiv (representativeCode (anchorRepresentative (Fin.ofNat 2222 (16*59+i.val))))) := by
  fin_cases i
  · exact anchorEntry0944_solved
  · exact anchorEntry0945_solved
  · exact anchorEntry0946_solved
  · exact anchorEntry0947_solved
  · exact anchorEntry0948_solved
  · exact anchorEntry0949_solved
  · exact anchorEntry0950_solved
  · exact anchorEntry0951_solved
  · exact anchorEntry0952_solved
  · exact anchorEntry0953_solved
  · exact anchorEntry0954_solved
  · exact anchorEntry0955_solved
  · exact anchorEntry0956_solved
  · exact anchorEntry0957_solved
  · exact anchorEntry0958_solved
  · exact anchorEntry0959_solved

end
end Holant.Pauli.ExoticKlein.SixPort
