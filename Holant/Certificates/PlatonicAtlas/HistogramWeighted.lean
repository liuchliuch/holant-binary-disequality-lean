import Holant.Certificates.PlatonicAtlas.HistogramCounts
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
local instance histogramWeightedPointDecidable : DecidableEq Point := Classical.decEq _
local instance histogramWeightedSubmoduleDecidable : DecidableEq (Submodule ℂ FourTensor) := Classical.decEq _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem index_weighted (K : ι→BinaryMatrix) (p : MatchingIndex ι)
    (hmax : ∀B∈secantFibers K p,B.card≤4) :
    indexMultiplicity K p 1+2*indexMultiplicity K p 2+
      3*indexMultiplicity K p 3+4*indexMultiplicity K p 4=3*(Fintype.card ι)^2-1 := by
  have h := fiberFamily_weighted_four (Finset.univ.erase p) (secantMap K p) hmax
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,
    MatchingIndex,Fintype.card_prod,Fintype.card_fin,pow_two,Nat.mul_assoc] using h

end
end Holant.Certificates.PlatonicAtlas
