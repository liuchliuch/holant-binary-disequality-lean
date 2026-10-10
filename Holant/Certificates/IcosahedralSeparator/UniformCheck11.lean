import Holant.Certificates.IcosahedralSeparator.UniformCheck10

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_11 : UniformRankCheck 11 := by decide +kernel
theorem uniformOutsideCheck_11 : UniformOutsideCheck 11 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
