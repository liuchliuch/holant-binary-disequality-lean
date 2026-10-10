import Holant.Certificates.IcosahedralSeparator.UniformCheck08

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_09 : UniformRankCheck 9 := by decide +kernel
theorem uniformOutsideCheck_09 : UniformOutsideCheck 9 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
