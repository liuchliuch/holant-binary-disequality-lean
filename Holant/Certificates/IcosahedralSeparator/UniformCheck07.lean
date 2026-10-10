import Holant.Certificates.IcosahedralSeparator.UniformCheck06

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_07 : UniformRankCheck 7 := by decide +kernel
theorem uniformOutsideCheck_07 : UniformOutsideCheck 7 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
