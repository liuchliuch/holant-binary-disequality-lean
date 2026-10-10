import Holant.Certificates.IcosahedralSeparator.UniformCheck22

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_23 : UniformRankCheck 23 := by decide +kernel
theorem uniformOutsideCheck_23 : UniformOutsideCheck 23 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
