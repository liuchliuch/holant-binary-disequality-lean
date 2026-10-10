import Holant.Certificates.IcosahedralSeparator.UniformCheck02

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_03 : UniformRankCheck 3 := by decide +kernel
theorem uniformOutsideCheck_03 : UniformOutsideCheck 3 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
