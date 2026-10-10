import Holant.Pauli.ExoticKlein.SixPortAtlasData

namespace Holant.Pauli.ExoticKlein.SixPort.Atlas
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option Elab.async false

theorem filterBatch00 (i : Fin 64) :
    Good (Fin.ofNat 960 (64*0+i.val)) ↔
      ∃ a : Fin 17, candidateIndex a = Fin.ofNat 960 (64*0+i.val) := by
  revert i
  decide +kernel

end
end Holant.Pauli.ExoticKlein.SixPort.Atlas
