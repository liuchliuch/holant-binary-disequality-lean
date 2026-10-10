import Holant.Certificates.IcosahedralSeparator.UniformCheck21

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_22 : UniformRankCheck 22 := by decide +kernel
theorem uniformOutsideCheck_22 : UniformOutsideCheck 22 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
