import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch00
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch01
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch02
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch03
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch04
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch05
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch06
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch07
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch08
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch09
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch10
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch11
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch12
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch13
import Holant.Pauli.ExoticKlein.SixPortAtlasFilter.Batch14

namespace Holant.Pauli.ExoticKlein.SixPort.Atlas
noncomputable section
set_option maxRecDepth 32768

theorem all_filter_batches (b : Fin 15) (i : Fin 64) :
    Good (Fin.ofNat 960 (64*b.val+i.val)) ↔
      ∃ a : Fin 17, candidateIndex a = Fin.ofNat 960 (64*b.val+i.val) := by
  fin_cases b
  · exact filterBatch00 i
  · exact filterBatch01 i
  · exact filterBatch02 i
  · exact filterBatch03 i
  · exact filterBatch04 i
  · exact filterBatch05 i
  · exact filterBatch06 i
  · exact filterBatch07 i
  · exact filterBatch08 i
  · exact filterBatch09 i
  · exact filterBatch10 i
  · exact filterBatch11 i
  · exact filterBatch12 i
  · exact filterBatch13 i
  · exact filterBatch14 i

theorem good_iff_candidate (j : Fin 960) : Good j ↔ ∃ a : Fin 17, candidateIndex a = j := by
  let b : Fin 15 := ⟨j.val/64,by have := j.isLt; omega⟩
  let i : Fin 64 := ⟨j.val%64,Nat.mod_lt _ (by decide)⟩
  have he : Fin.ofNat 960 (64*b.val+i.val) = j := by
    apply Fin.ext
    change (64*(j.val/64)+j.val%64)%960 = j.val
    have h : 64*(j.val/64)+j.val%64 = j.val := by omega
    rw [h,Nat.mod_eq_of_lt j.isLt]
  simpa only [he] using all_filter_batches b i

 theorem candidate_good (i : Fin 17) : Good (candidateIndex i) :=
  (good_iff_candidate _).mpr ⟨i,rfl⟩

end
end Holant.Pauli.ExoticKlein.SixPort.Atlas
