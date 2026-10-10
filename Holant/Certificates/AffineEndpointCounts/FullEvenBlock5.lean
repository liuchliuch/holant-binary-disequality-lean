import Holant.Certificates.AffineEndpointCounts.FullEvenChecks

namespace Holant.Certificates.AffineEndpointCounts
open Holant.Certificates.AffineReference
set_option maxRecDepth 200000
set_option maxHeartbeats 100000000

theorem fullEvenBlock5_first : ∀ a b c : Fin 4,
    FirstEvenWitness ((a,b,c),true,false,true) (witnessBlock5 (phaseIndex (a,b,c))) := by decide +kernel

end Holant.Certificates.AffineEndpointCounts
