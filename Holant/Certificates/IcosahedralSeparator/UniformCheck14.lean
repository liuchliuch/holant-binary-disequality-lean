import Holant.Certificates.IcosahedralSeparator.UniformCheck13

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_14 : UniformRankCheck 14 := by decide +kernel
theorem uniformOutsideCheck_14 : UniformOutsideCheck 14 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
