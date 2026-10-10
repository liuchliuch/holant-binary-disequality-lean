import Holant.Pauli.ExoticKlein.SixPortCachedIntegerProblem
import Holant.Pauli.ExoticKlein.SixPortAnchorWitness
import Holant.Pauli.ExoticKlein.SixPortIntegerBatches.Batch002
import Holant.Pauli.ExoticKlein.SixPortIntegerBatches.Batch003

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open IntegerCertificate
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

theorem anchorEntry0032_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 32))) := by
  have he : anchorRepresentative 32 = 39 := by decide +kernel
  rw [he]
  exact irep0039_representative

theorem anchorEntry0033_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 33))) := by
  have he : anchorRepresentative 33 = 40 := by decide +kernel
  rw [he]
  exact irep0040_representative

theorem anchorEntry0034_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 34))) := by
  have he : anchorRepresentative 34 = 41 := by decide +kernel
  rw [he]
  exact irep0041_representative

theorem anchorEntry0035_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 35))) := by
  have he : anchorRepresentative 35 = 42 := by decide +kernel
  rw [he]
  exact irep0042_representative

theorem anchorEntry0036_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 36))) := by
  have he : anchorRepresentative 36 = 43 := by decide +kernel
  rw [he]
  exact irep0043_representative

theorem anchorEntry0037_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 37))) := by
  have he : anchorRepresentative 37 = 44 := by decide +kernel
  rw [he]
  exact irep0044_representative

theorem anchorEntry0038_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 38))) := by
  have he : anchorRepresentative 38 = 45 := by decide +kernel
  rw [he]
  exact irep0045_representative

theorem anchorEntry0039_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 39))) := by
  have he : anchorRepresentative 39 = 46 := by decide +kernel
  rw [he]
  exact irep0046_representative

theorem anchorEntry0040_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 40))) := by
  have he : anchorRepresentative 40 = 47 := by decide +kernel
  rw [he]
  exact irep0047_representative

theorem anchorEntry0041_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 41))) := by
  have he : anchorRepresentative 41 = 48 := by decide +kernel
  rw [he]
  exact irep0048_representative

theorem anchorEntry0042_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 42))) := by
  have he : anchorRepresentative 42 = 49 := by decide +kernel
  rw [he]
  exact irep0049_representative

theorem anchorEntry0043_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 43))) := by
  have he : anchorRepresentative 43 = 54 := by decide +kernel
  rw [he]
  exact irep0054_representative

theorem anchorEntry0044_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 44))) := by
  have he : anchorRepresentative 44 = 55 := by decide +kernel
  rw [he]
  exact irep0055_representative

theorem anchorEntry0045_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 45))) := by
  have he : anchorRepresentative 45 = 56 := by decide +kernel
  rw [he]
  exact irep0056_representative

theorem anchorEntry0046_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 46))) := by
  have he : anchorRepresentative 46 = 57 := by decide +kernel
  rw [he]
  exact irep0057_representative

theorem anchorEntry0047_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 47))) := by
  have he : anchorRepresentative 47 = 58 := by decide +kernel
  rw [he]
  exact irep0058_representative

theorem anchorBatch002 (i : Fin 16) :
    Solved (stateEquiv (representativeCode (anchorRepresentative (Fin.ofNat 2222 (16*2+i.val))))) := by
  fin_cases i
  · exact anchorEntry0032_solved
  · exact anchorEntry0033_solved
  · exact anchorEntry0034_solved
  · exact anchorEntry0035_solved
  · exact anchorEntry0036_solved
  · exact anchorEntry0037_solved
  · exact anchorEntry0038_solved
  · exact anchorEntry0039_solved
  · exact anchorEntry0040_solved
  · exact anchorEntry0041_solved
  · exact anchorEntry0042_solved
  · exact anchorEntry0043_solved
  · exact anchorEntry0044_solved
  · exact anchorEntry0045_solved
  · exact anchorEntry0046_solved
  · exact anchorEntry0047_solved

end
end Holant.Pauli.ExoticKlein.SixPort
