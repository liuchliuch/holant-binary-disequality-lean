import Holant.Certificates.EqualityQuaternary.KleinRepresentative

namespace Holant.Certificates.EqualityQuaternary.Klein.Orbit
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem orbitCheck07 : OrbitCheck 7 := by
  unfold OrbitCheck
  decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Orbit
