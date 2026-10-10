import Holant.Certificates.IcosahedralSeparator.UniformCheck23

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_24 : UniformRankCheck 24 := by decide +kernel
theorem uniformOutsideCheck_24 : UniformOutsideCheck 24 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
