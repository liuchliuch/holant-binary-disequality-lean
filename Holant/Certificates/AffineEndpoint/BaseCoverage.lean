import Holant.Certificates.AffineEndpoint.BaseCoverageFalse
import Holant.Certificates.AffineEndpoint.BaseCoverageTrue

/-! Exhaustive coverage of the two actual non-affine base actions. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
 theorem all_base_inputs (b : Bool) (c : InputCode) : ∃w,BaseWitnessCheck c.1 c.2.val b w := by
  cases b
  · exact base_inputs_false c
  · exact base_inputs_true c
end Holant.Certificates.AffineEndpoint.BaseCertificate
