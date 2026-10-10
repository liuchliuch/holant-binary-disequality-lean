import Holant.Certificates.IcosahedralSeparator.UniformCheck24

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_25 : UniformRankCheck 25 := by decide +kernel
theorem uniformOutsideCheck_25 : UniformOutsideCheck 25 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
