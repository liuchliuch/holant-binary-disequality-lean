import Holant.Certificates.PlatonicAtlas.HistogramShapes
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
local instance histogramCountsPointDecidable : DecidableEq Point := Classical.decEq _
local instance histogramCountsSubmoduleDecidable : DecidableEq (Submodule ℂ FourTensor) := Classical.decEq _

 def standardBase (g : PlatonicModel) : MatchingIndex (Fin (size g)) :=
  (0,identityIndex g,identityIndex g)

 theorem standard_index_rich (g : PlatonicModel) (n : ℕ) (hn : 2≤n) :
    indexMultiplicity (representative g) (standardBase g) n=
      2*(linesThrough g (identityIndex g) (n+1)).card+(if n+1=3 then size g else 0) := by
  have hp : configurationPoint (representative g) (representative_det_ne_zero g) (standardBase g)=basePoint 0 :=
    (basePoint_zero_eq_deck g).symm
  rw [indexMultiplicity_rich _ (representative_det_ne_zero g) (representative_proportional_faithful g) _ _ hn,hp,
    standard_actual_rich_incidences _ _ (by omega)]

 theorem external_index_rich : indexMultiplicity External.representative (0,0,0) 2=8 := by
  exact (indexMultiplicity_rich External.representative External.representative_det_ne_zero
    external_representative_faithful (0,0,0) 2 (by decide)).trans external_actual_rich_incidences

 theorem octahedral_index_rich :
    indexMultiplicity (representative .octahedral) (standardBase .octahedral) 2=32 ∧
    indexMultiplicity (representative .octahedral) (standardBase .octahedral) 3=6 := by
  rw [standard_index_rich _ 2 (by decide),standard_index_rich _ 3 (by decide),
    (octahedral_point_incidences _).1,(octahedral_point_incidences _).2]
  decide

 theorem icosahedral_index_rich :
    indexMultiplicity (representative .icosahedral) (standardBase .icosahedral) 2=80 ∧
    indexMultiplicity (representative .icosahedral) (standardBase .icosahedral) 4=12 := by
  rw [standard_index_rich _ 2 (by decide),standard_index_rich _ 4 (by decide),
    (icosahedral_point_incidences _).1,(icosahedral_point_incidences _).2]
  decide


end
end Holant.Certificates.PlatonicAtlas
