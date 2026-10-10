import Holant.Certificates.AffineEndpointCounts.RetainedData
namespace Holant.Certificates.AffineEndpointCounts
open Holant.Certificates.AffineEndpoint
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem candidate_retained : ∀b j, BaseRetained (candidateInput b j).1 (candidateInput b j).2.val b := by decide +kernel

end Holant.Certificates.AffineEndpointCounts
