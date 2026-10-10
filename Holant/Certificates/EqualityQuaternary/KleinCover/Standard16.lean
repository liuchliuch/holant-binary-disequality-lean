import Holant.Certificates.EqualityQuaternary.KleinFiniteData

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace standard16
def rows0 : List Row := []
theorem cover0 : Covers (standardProblem 16) rows0 := by
  exact covers_target (standardProblem 16) rows0 1 ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]] (by decide +kernel)
theorem root : Covers (standardProblem 16) [] := cover0
end standard16
end Holant.Certificates.EqualityQuaternary.Klein.Finite
