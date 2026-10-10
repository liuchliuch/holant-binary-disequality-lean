import Holant.Certificates.IcosahedralSeparator.UniformCheck05

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_06 : UniformRankCheck 6 := by decide +kernel
theorem uniformOutsideCheck_06 : UniformOutsideCheck 6 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
