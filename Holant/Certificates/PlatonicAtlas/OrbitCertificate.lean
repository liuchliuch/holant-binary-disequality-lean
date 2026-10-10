import Holant.Certificates.PlatonicAtlas.OrbitTetrahedral
import Holant.Certificates.PlatonicAtlas.OrbitOctahedral
import Holant.Certificates.PlatonicAtlas.OrbitIcosahedral

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem base_orbit_certificate (g : PlatonicModel) (b : Fin (baseCount g)) : BaseOrbitEntry g b := by
  cases g
  · fin_cases b
    · exact tetrahedral_base_orbit_0
    · exact tetrahedral_base_orbit_1
    · exact tetrahedral_base_orbit_2
    · exact tetrahedral_base_orbit_3
    · exact tetrahedral_base_orbit_4
    · exact tetrahedral_base_orbit_5
    · exact tetrahedral_base_orbit_6
  · fin_cases b
    · exact octahedral_base_orbit_0
    · exact octahedral_base_orbit_1
    · exact octahedral_base_orbit_2
    · exact octahedral_base_orbit_3
    · exact octahedral_base_orbit_4
    · exact octahedral_base_orbit_5
    · exact octahedral_base_orbit_6
    · exact octahedral_base_orbit_7
    · exact octahedral_base_orbit_8
    · exact octahedral_base_orbit_9
    · exact octahedral_base_orbit_10
    · exact octahedral_base_orbit_11
    · exact octahedral_base_orbit_12
  · fin_cases b
    · exact icosahedral_base_orbit_0
    · exact icosahedral_base_orbit_1
    · exact icosahedral_base_orbit_2
    · exact icosahedral_base_orbit_3
    · exact icosahedral_base_orbit_4
    · exact icosahedral_base_orbit_5
    · exact icosahedral_base_orbit_6
    · exact icosahedral_base_orbit_7
    · exact icosahedral_base_orbit_8
    · exact icosahedral_base_orbit_9
    · exact icosahedral_base_orbit_10
    · exact icosahedral_base_orbit_11
    · exact icosahedral_base_orbit_12
    · exact icosahedral_base_orbit_13
    · exact icosahedral_base_orbit_14
    · exact icosahedral_base_orbit_15
    · exact icosahedral_base_orbit_16
    · exact icosahedral_base_orbit_17
    · exact icosahedral_base_orbit_18
    · exact icosahedral_base_orbit_19
    · exact icosahedral_base_orbit_20
    · exact icosahedral_base_orbit_21
    · exact icosahedral_base_orbit_22
    · exact icosahedral_base_orbit_23
    · exact icosahedral_base_orbit_24
    · exact icosahedral_base_orbit_25
    · exact icosahedral_base_orbit_26
    · exact icosahedral_base_orbit_27
    · exact icosahedral_base_orbit_28
    · exact icosahedral_base_orbit_29
    · exact icosahedral_base_orbit_30

end Holant.Certificates.PlatonicAtlas
