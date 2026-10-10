import Holant.Pauli.ExoticKlein.SixPortCachedIntegerProblem
import Holant.Pauli.ExoticKlein.SixPortAnchorWitness
import Holant.Pauli.ExoticKlein.SixPortIntegerBatches.Batch001
import Holant.Pauli.ExoticKlein.SixPortIntegerBatches.Batch002

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open IntegerCertificate
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

theorem anchorEntry0016_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 16))) := by
  have he : anchorRepresentative 16 = 17 := by decide +kernel
  rw [he]
  exact irep0017_representative

theorem anchorEntry0017_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 17))) := by
  have he : anchorRepresentative 17 = 18 := by decide +kernel
  rw [he]
  exact irep0018_representative

theorem anchorEntry0018_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 18))) := by
  have he : anchorRepresentative 18 = 19 := by decide +kernel
  rw [he]
  exact irep0019_representative

theorem anchorEntry0019_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 19))) := by
  have he : anchorRepresentative 19 = 22 := by decide +kernel
  rw [he]
  exact irep0022_representative

theorem anchorEntry0020_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 20))) := by
  have he : anchorRepresentative 20 = 23 := by decide +kernel
  rw [he]
  exact irep0023_representative

theorem anchorEntry0021_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 21))) := by
  have he : anchorRepresentative 21 = 24 := by decide +kernel
  rw [he]
  exact irep0024_representative

theorem anchorEntry0022_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 22))) := by
  have he : anchorRepresentative 22 = 25 := by decide +kernel
  rw [he]
  exact irep0025_representative

theorem anchorEntry0023_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 23))) := by
  have he : anchorRepresentative 23 = 26 := by decide +kernel
  rw [he]
  exact irep0026_representative

theorem anchorEntry0024_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 24))) := by
  have he : anchorRepresentative 24 = 27 := by decide +kernel
  rw [he]
  exact irep0027_representative

theorem anchorEntry0025_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 25))) := by
  have he : anchorRepresentative 25 = 28 := by decide +kernel
  rw [he]
  exact irep0028_representative

theorem anchorEntry0026_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 26))) := by
  have he : anchorRepresentative 26 = 29 := by decide +kernel
  rw [he]
  exact irep0029_representative

theorem anchorEntry0027_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 27))) := by
  have he : anchorRepresentative 27 = 30 := by decide +kernel
  rw [he]
  exact irep0030_representative

theorem anchorEntry0028_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 28))) := by
  have he : anchorRepresentative 28 = 31 := by decide +kernel
  rw [he]
  exact irep0031_representative

theorem anchorEntry0029_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 29))) := by
  have he : anchorRepresentative 29 = 32 := by decide +kernel
  rw [he]
  exact irep0032_representative

theorem anchorEntry0030_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 30))) := by
  have he : anchorRepresentative 30 = 36 := by decide +kernel
  rw [he]
  exact irep0036_representative

theorem anchorEntry0031_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 31))) := by
  have he : anchorRepresentative 31 = 37 := by decide +kernel
  rw [he]
  exact irep0037_representative

theorem anchorBatch001 (i : Fin 16) :
    Solved (stateEquiv (representativeCode (anchorRepresentative (Fin.ofNat 2222 (16*1+i.val))))) := by
  fin_cases i
  · exact anchorEntry0016_solved
  · exact anchorEntry0017_solved
  · exact anchorEntry0018_solved
  · exact anchorEntry0019_solved
  · exact anchorEntry0020_solved
  · exact anchorEntry0021_solved
  · exact anchorEntry0022_solved
  · exact anchorEntry0023_solved
  · exact anchorEntry0024_solved
  · exact anchorEntry0025_solved
  · exact anchorEntry0026_solved
  · exact anchorEntry0027_solved
  · exact anchorEntry0028_solved
  · exact anchorEntry0029_solved
  · exact anchorEntry0030_solved
  · exact anchorEntry0031_solved

end
end Holant.Pauli.ExoticKlein.SixPort
