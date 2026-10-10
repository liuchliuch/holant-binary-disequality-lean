import Holant.Certificates.OctahedralSeparator.TensorData

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.OctahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def primeInitialScalar : Fin 3→Signature Scalar 4 :=
  ![p0 (theta 1 (q 0)) (theta 1 (q 0)),p1 (theta 1 (q 1)) (theta 1 (q 1)),
    p2 (theta 1 (q 2)) (theta 1 (q 2))]
def primeScaleScalar : Fin 3→Scalar := ![1,-1,-1]

theorem prime_initial_certificate : ∀r : Fin 3,
    Signature.coordinateAction (coefficientLegs 1) (![aTensor,bTensor,cTensor] r)=
      tensorScale (primeScaleScalar r) (primeInitialScalar r) := by
  intro r
  fin_cases r <;> decide +kernel


end Holant.Certificates.RainbowOrbit
