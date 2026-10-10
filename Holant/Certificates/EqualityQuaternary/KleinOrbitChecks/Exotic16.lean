import Holant.Certificates.EqualityQuaternary.KleinRepresentative

namespace Holant.Certificates.EqualityQuaternary.Klein.Orbit
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem orbitCheck16 : OrbitCheck 16 := by
  unfold OrbitCheck
  decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Orbit
