import Holant.Certificates.AffineEndpoint.CoreTensorData

namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Certificates.OctahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

 theorem coreClearingScale_ne_zero : ∀k,coreClearingScale k≠0 := by decide +kernel

 theorem coreTensorRows_correct : ∀k x y,IntegerCoefficient.eval (coreTensorRows k x y)=
    coreClearingScale k^4*(∏j : Fin 4,coreRaw (numberedCore k) (codeWord x j) (codeWord y j)) := by
  intro k
  fin_cases k <;> decide +kernel

end Holant.Certificates.AffineEndpoint
