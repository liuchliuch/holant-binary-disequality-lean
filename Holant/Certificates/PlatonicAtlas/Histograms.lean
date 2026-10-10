import Holant.Certificates.PlatonicAtlas.HistogramWeighted
import Holant.Certificates.PlatonicAtlas.RichIncidenceCounts

/-! The three source quotient histograms, derived from the complete actual
secant partition and the established rich-line incidences. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable
local instance histogramsPointDecidable : DecidableEq Point := Classical.decEq _
local instance histogramsSubmoduleDecidable : DecidableEq (Submodule ℂ FourTensor) := Classical.decEq _

 theorem external_index_histogram :
    indexMultiplicity External.representative (0,0,0) 1=415 ∧
    indexMultiplicity External.representative (0,0,0) 2=8 ∧
    ∀n,n≠1→n≠2→indexMultiplicity External.representative (0,0,0) n=0 := by
  have hz (n : ℕ) (h1 : n≠1) (h2 : n≠2) : indexMultiplicity External.representative (0,0,0) n=0 := by
    apply fiberMultiplicity_zero
    intro B hB
    rcases external_fiber_sizes (0,0,0) B hB with h|h <;> omega
  have hs := index_weighted External.representative (0,0,0) (fun B hB => by
      rcases external_fiber_sizes (0,0,0) B hB with h|h <;> omega)
  change indexMultiplicity External.representative (0,0,0) 1+
    2*indexMultiplicity External.representative (0,0,0) 2+
    3*indexMultiplicity External.representative (0,0,0) 3+
    4*indexMultiplicity External.representative (0,0,0) 4=431 at hs
  rw [external_index_rich,hz 3 (by decide) (by decide),hz 4 (by decide) (by decide)] at hs
  exact ⟨by omega,external_index_rich,hz⟩

 theorem octahedral_index_histogram :
    indexMultiplicity (representative .octahedral) (standardBase .octahedral) 1=1645 ∧
    indexMultiplicity (representative .octahedral) (standardBase .octahedral) 2=32 ∧
    indexMultiplicity (representative .octahedral) (standardBase .octahedral) 3=6 ∧
    ∀n,n≠1→n≠2→n≠3→indexMultiplicity (representative .octahedral) (standardBase .octahedral) n=0 := by
  have hz (n : ℕ) (h1 : n≠1) (h2 : n≠2) (h3 : n≠3) :
      indexMultiplicity (representative .octahedral) (standardBase .octahedral) n=0 := by
    apply fiberMultiplicity_zero
    intro B hB
    have hh := standard_fiber_sizes .octahedral (standardBase .octahedral) B hB
    simp only at hh
    omega
  have hs := index_weighted (representative .octahedral) (standardBase .octahedral) (fun B hB => by
      have hh := standard_fiber_sizes .octahedral (standardBase .octahedral) B hB
      simp only at hh
      omega)
  change indexMultiplicity (representative .octahedral) (standardBase .octahedral) 1+
    2*indexMultiplicity (representative .octahedral) (standardBase .octahedral) 2+
    3*indexMultiplicity (representative .octahedral) (standardBase .octahedral) 3+
    4*indexMultiplicity (representative .octahedral) (standardBase .octahedral) 4=1727 at hs
  rw [octahedral_index_rich.1,octahedral_index_rich.2,hz 4 (by decide) (by decide) (by decide)] at hs
  exact ⟨by omega,octahedral_index_rich.1,octahedral_index_rich.2,hz⟩

 theorem icosahedral_index_histogram :
    indexMultiplicity (representative .icosahedral) (standardBase .icosahedral) 1=10591 ∧
    indexMultiplicity (representative .icosahedral) (standardBase .icosahedral) 2=80 ∧
    indexMultiplicity (representative .icosahedral) (standardBase .icosahedral) 4=12 ∧
    ∀n,n≠1→n≠2→n≠4→indexMultiplicity (representative .icosahedral) (standardBase .icosahedral) n=0 := by
  have hz (n : ℕ) (h1 : n≠1) (h2 : n≠2) (h4 : n≠4) :
      indexMultiplicity (representative .icosahedral) (standardBase .icosahedral) n=0 := by
    apply fiberMultiplicity_zero
    intro B hB
    have hh := standard_fiber_sizes .icosahedral (standardBase .icosahedral) B hB
    simp only at hh
    omega
  have hs := index_weighted (representative .icosahedral) (standardBase .icosahedral) (fun B hB => by
      have hh := standard_fiber_sizes .icosahedral (standardBase .icosahedral) B hB
      simp only at hh
      omega)
  change indexMultiplicity (representative .icosahedral) (standardBase .icosahedral) 1+
    2*indexMultiplicity (representative .icosahedral) (standardBase .icosahedral) 2+
    3*indexMultiplicity (representative .icosahedral) (standardBase .icosahedral) 3+
    4*indexMultiplicity (representative .icosahedral) (standardBase .icosahedral) 4=10799 at hs
  rw [icosahedral_index_rich.1,icosahedral_index_rich.2,hz 3 (by decide) (by decide) (by decide)] at hs
  exact ⟨by omega,icosahedral_index_rich.1,icosahedral_index_rich.2,hz⟩

end
end Holant.Certificates.PlatonicAtlas
