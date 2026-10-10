import Holant.Certificates.EqualityQuaternary.KleinFiniteData

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace standard07
def rows0 : List Row := []
theorem cover0 : Covers (standardProblem 7) rows0 := by
  exact covers_target (standardProblem 7) rows0 2 ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]] (by decide +kernel)
theorem root : Covers (standardProblem 7) [] := cover0
end standard07
end Holant.Certificates.EqualityQuaternary.Klein.Finite
