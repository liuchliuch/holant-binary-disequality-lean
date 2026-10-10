import Holant.Certificates.IcosahedralSeparator.UniformCheck26

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_27 : UniformRankCheck 27 := by decide +kernel
theorem uniformOutsideCheck_27 : UniformOutsideCheck 27 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
