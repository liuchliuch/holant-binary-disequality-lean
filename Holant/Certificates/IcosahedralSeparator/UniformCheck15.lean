import Holant.Certificates.IcosahedralSeparator.UniformCheck14

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_15 : UniformRankCheck 15 := by decide +kernel
theorem uniformOutsideCheck_15 : UniformOutsideCheck 15 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
