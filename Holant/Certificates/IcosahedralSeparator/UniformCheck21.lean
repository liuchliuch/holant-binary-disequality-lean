import Holant.Certificates.IcosahedralSeparator.UniformCheck20

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_21 : UniformRankCheck 21 := by decide +kernel
theorem uniformOutsideCheck_21 : UniformOutsideCheck 21 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
