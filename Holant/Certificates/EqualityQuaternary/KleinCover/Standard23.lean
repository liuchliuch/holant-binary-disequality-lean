import Holant.Certificates.EqualityQuaternary.KleinFiniteData

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace standard23
def rows0 : List Row := []
theorem cover0 : Covers (standardProblem 23) rows0 := by
  exact covers_target (standardProblem 23) rows0 0 ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]] (by decide +kernel)
theorem root : Covers (standardProblem 23) [] := cover0
end standard23
end Holant.Certificates.EqualityQuaternary.Klein.Finite
