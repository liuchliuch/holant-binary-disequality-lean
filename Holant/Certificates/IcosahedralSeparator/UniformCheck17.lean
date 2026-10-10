import Holant.Certificates.IcosahedralSeparator.UniformCheck16

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_17 : UniformRankCheck 17 := by decide +kernel
theorem uniformOutsideCheck_17 : UniformOutsideCheck 17 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
