import Holant.Pauli.ExoticKlein.SixPortCachedIntegerProblem
import Holant.Pauli.ExoticKlein.SixPortAnchorWitness
import Holant.Pauli.ExoticKlein.SixPortIntegerBatches.Batch000
import Holant.Pauli.ExoticKlein.SixPortIntegerBatches.Batch001

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open IntegerCertificate
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

theorem anchorEntry0000_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 0))) := by
  have he : anchorRepresentative 0 = 0 := by decide +kernel
  rw [he]
  exact irep0000_representative

theorem anchorEntry0001_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1))) := by
  have he : anchorRepresentative 1 = 1 := by decide +kernel
  rw [he]
  exact irep0001_representative

theorem anchorEntry0002_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2))) := by
  have he : anchorRepresentative 2 = 2 := by decide +kernel
  rw [he]
  exact irep0002_representative

theorem anchorEntry0003_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 3))) := by
  have he : anchorRepresentative 3 = 3 := by decide +kernel
  rw [he]
  exact irep0003_representative

theorem anchorEntry0004_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 4))) := by
  have he : anchorRepresentative 4 = 4 := by decide +kernel
  rw [he]
  exact irep0004_representative

theorem anchorEntry0005_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 5))) := by
  have he : anchorRepresentative 5 = 5 := by decide +kernel
  rw [he]
  exact irep0005_representative

theorem anchorEntry0006_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 6))) := by
  have he : anchorRepresentative 6 = 6 := by decide +kernel
  rw [he]
  exact irep0006_representative

theorem anchorEntry0007_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 7))) := by
  have he : anchorRepresentative 7 = 7 := by decide +kernel
  rw [he]
  exact irep0007_representative

theorem anchorEntry0008_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 8))) := by
  have he : anchorRepresentative 8 = 8 := by decide +kernel
  rw [he]
  exact irep0008_representative

theorem anchorEntry0009_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 9))) := by
  have he : anchorRepresentative 9 = 9 := by decide +kernel
  rw [he]
  exact irep0009_representative

theorem anchorEntry0010_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 10))) := by
  have he : anchorRepresentative 10 = 11 := by decide +kernel
  rw [he]
  exact irep0011_representative

theorem anchorEntry0011_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 11))) := by
  have he : anchorRepresentative 11 = 12 := by decide +kernel
  rw [he]
  exact irep0012_representative

theorem anchorEntry0012_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 12))) := by
  have he : anchorRepresentative 12 = 13 := by decide +kernel
  rw [he]
  exact irep0013_representative

theorem anchorEntry0013_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 13))) := by
  have he : anchorRepresentative 13 = 14 := by decide +kernel
  rw [he]
  exact irep0014_representative

theorem anchorEntry0014_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 14))) := by
  have he : anchorRepresentative 14 = 15 := by decide +kernel
  rw [he]
  exact irep0015_representative

theorem anchorEntry0015_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 15))) := by
  have he : anchorRepresentative 15 = 16 := by decide +kernel
  rw [he]
  exact irep0016_representative

theorem anchorBatch000 (i : Fin 16) :
    Solved (stateEquiv (representativeCode (anchorRepresentative (Fin.ofNat 2222 (16*0+i.val))))) := by
  fin_cases i
  · exact anchorEntry0000_solved
  · exact anchorEntry0001_solved
  · exact anchorEntry0002_solved
  · exact anchorEntry0003_solved
  · exact anchorEntry0004_solved
  · exact anchorEntry0005_solved
  · exact anchorEntry0006_solved
  · exact anchorEntry0007_solved
  · exact anchorEntry0008_solved
  · exact anchorEntry0009_solved
  · exact anchorEntry0010_solved
  · exact anchorEntry0011_solved
  · exact anchorEntry0012_solved
  · exact anchorEntry0013_solved
  · exact anchorEntry0014_solved
  · exact anchorEntry0015_solved

end
end Holant.Pauli.ExoticKlein.SixPort
