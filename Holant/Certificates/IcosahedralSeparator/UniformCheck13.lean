import Holant.Certificates.IcosahedralSeparator.UniformCheck12

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_13 : UniformRankCheck 13 := by decide +kernel
theorem uniformOutsideCheck_13 : UniformOutsideCheck 13 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
