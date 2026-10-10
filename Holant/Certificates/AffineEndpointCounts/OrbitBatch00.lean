import Holant.Certificates.AffineEndpointCounts.OrbitData
namespace Holant.Certificates.AffineEndpointCounts
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem orbit_batch_00 : ∀j : Fin 16, orbitRowCheck ⟨0+j.val,by omega⟩ = true := by decide +kernel
end Holant.Certificates.AffineEndpointCounts
