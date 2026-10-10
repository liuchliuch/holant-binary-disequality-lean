import Holant.Certificates.PlatonicAtlas.OrbitData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem tetrahedral_base_orbit_0 : BaseOrbitEntry .tetrahedral (0 : Fin 7) := by decide +kernel

theorem tetrahedral_base_orbit_1 : BaseOrbitEntry .tetrahedral (1 : Fin 7) := by decide +kernel

theorem tetrahedral_base_orbit_2 : BaseOrbitEntry .tetrahedral (2 : Fin 7) := by decide +kernel

theorem tetrahedral_base_orbit_3 : BaseOrbitEntry .tetrahedral (3 : Fin 7) := by decide +kernel

theorem tetrahedral_base_orbit_4 : BaseOrbitEntry .tetrahedral (4 : Fin 7) := by decide +kernel

theorem tetrahedral_base_orbit_5 : BaseOrbitEntry .tetrahedral (5 : Fin 7) := by decide +kernel

theorem tetrahedral_base_orbit_6 : BaseOrbitEntry .tetrahedral (6 : Fin 7) := by decide +kernel

end Holant.Certificates.PlatonicAtlas
