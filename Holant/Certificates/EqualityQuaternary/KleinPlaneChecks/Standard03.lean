import Holant.Certificates.EqualityQuaternary.StandardKleinPlaneData

namespace Holant.Certificates.EqualityQuaternary.Klein
open Holant.Marked.SupportAtlas Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardSupportQ03 : ∀ (r : Fin 4) (i : Fin 16),
    parity (word i)≠standardParity 3 → planeTensorQ .standard (3 : Fin 4) r (word i)=0 := by decide +kernel

theorem standardComplementQ03 : ∀ (r : Fin 4) (i : Fin 16),
    planeTensorQ .standard (3 : Fin 4) r (complement (word i))=
      standardSignQ 3*planeTensorQ .standard (3 : Fin 4) r (word i) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein
