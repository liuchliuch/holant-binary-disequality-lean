import Holant.Certificates.AffineEndpoint.BaseTensorData
namespace Holant.Certificates.AffineEndpoint
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem baseTensor_eq : ∀b x y,baseTensor b x y=coreTensorRows (baseCore b) x y := by
  intro b x
  cases b <;> fin_cases x <;> decide +kernel
end Holant.Certificates.AffineEndpoint
