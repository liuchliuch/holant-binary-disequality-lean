import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic00
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic01
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic02
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic03
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic04
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic05
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic06
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic07
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic08
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic09
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic10
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic11
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic12
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic13
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic14
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic15
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic16
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic17
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic18
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic19
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic20
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic21
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic22
import Holant.Certificates.EqualityQuaternary.KleinOrbitChecks.Exotic23

namespace Holant.Certificates.EqualityQuaternary.Klein.Orbit

theorem all_orbit_checks (j : Fin 24) : OrbitCheck j := by
  fin_cases j
  · exact orbitCheck00
  · exact orbitCheck01
  · exact orbitCheck02
  · exact orbitCheck03
  · exact orbitCheck04
  · exact orbitCheck05
  · exact orbitCheck06
  · exact orbitCheck07
  · exact orbitCheck08
  · exact orbitCheck09
  · exact orbitCheck10
  · exact orbitCheck11
  · exact orbitCheck12
  · exact orbitCheck13
  · exact orbitCheck14
  · exact orbitCheck15
  · exact orbitCheck16
  · exact orbitCheck17
  · exact orbitCheck18
  · exact orbitCheck19
  · exact orbitCheck20
  · exact orbitCheck21
  · exact orbitCheck22
  · exact orbitCheck23

end Holant.Certificates.EqualityQuaternary.Klein.Orbit
