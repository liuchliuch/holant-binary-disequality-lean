import Holant.Certificates.IcosahedralSeparator.UniformCheck17

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_18 : UniformRankCheck 18 := by decide +kernel
theorem uniformOutsideCheck_18 : UniformOutsideCheck 18 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
