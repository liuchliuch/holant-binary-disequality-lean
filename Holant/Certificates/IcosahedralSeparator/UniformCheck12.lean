import Holant.Certificates.IcosahedralSeparator.UniformCheck11

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_12 : UniformRankCheck 12 := by decide +kernel
theorem uniformOutsideCheck_12 : UniformOutsideCheck 12 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
