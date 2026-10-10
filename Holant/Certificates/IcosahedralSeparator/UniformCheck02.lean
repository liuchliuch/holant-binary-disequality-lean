import Holant.Certificates.IcosahedralSeparator.UniformCheck01

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_02 : UniformRankCheck 2 := by decide +kernel
theorem uniformOutsideCheck_02 : UniformOutsideCheck 2 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
