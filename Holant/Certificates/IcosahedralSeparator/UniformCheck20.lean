import Holant.Certificates.IcosahedralSeparator.UniformCheck19

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_20 : UniformRankCheck 20 := by decide +kernel
theorem uniformOutsideCheck_20 : UniformOutsideCheck 20 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
