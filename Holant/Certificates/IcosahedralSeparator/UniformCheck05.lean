import Holant.Certificates.IcosahedralSeparator.UniformCheck04

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_05 : UniformRankCheck 5 := by decide +kernel
theorem uniformOutsideCheck_05 : UniformOutsideCheck 5 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
