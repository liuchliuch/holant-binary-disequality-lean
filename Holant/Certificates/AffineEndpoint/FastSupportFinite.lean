import Holant.Certificates.AffineEndpoint.FastSupportData
namespace Holant.Certificates.AffineEndpoint
open Holant.Tractable.AffinePhase SupportCatalog
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 theorem fastSupportDimension_eq : ∀s,fastSupportDimension s=supportDim s := by decide +kernel
 theorem fastSupportLinear_eq : ∀s,fastSupportLinear s=supportLinearIndex s := by decide +kernel
 theorem fastSupportOrigin_eq : ∀s,fastSupportOrigin s=(supportRows s).originCode := by decide +kernel
 theorem fastSupportMask_eq : ∀s,fastSupportMask s=(supportRows s).mask.val := by decide +kernel
 theorem fastLinearCoordinates_eq : ∀l x,∀j : Fin (linearDim l),
    (fastLinearCoordinates l x).val.testBit j.val=linearCoordinates l (codeWord x) j := by
  intro l
  fin_cases l <;> decide +kernel
end Holant.Certificates.AffineEndpoint
