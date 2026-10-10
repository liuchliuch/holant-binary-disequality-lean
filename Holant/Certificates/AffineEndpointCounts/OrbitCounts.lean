import Holant.Certificates.AffineEndpointCounts.OrbitSemantics
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Certificates.AffineEndpoint
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

-- This is a check of the exact keys whose semantic equality was proved above.
theorem reference_key_histogram :
    (referenceKeySet 2).card = 1 ∧ (referenceKeySet 4).card = 24 ∧
      (referenceKeySet 8).card = 256 := by decide +kernel

theorem reference_invariant_histogram :
    (referenceInvariantSet 2).ncard = 1 ∧ (referenceInvariantSet 4).ncard = 24 ∧
      (referenceInvariantSet 8).ncard = 256 := by
  simpa only [referenceInvariant_count] using reference_key_histogram

end Holant.Certificates.AffineEndpointCounts
