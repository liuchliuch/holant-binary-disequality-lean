import Holant.Certificates.IcosahedralSeparator.UniformCheck25

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_26 : UniformRankCheck 26 := by decide +kernel
theorem uniformOutsideCheck_26 : UniformOutsideCheck 26 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
