import Holant.Certificates.IcosahedralSeparator.UniformCheck18

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_19 : UniformRankCheck 19 := by decide +kernel
theorem uniformOutsideCheck_19 : UniformOutsideCheck 19 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
