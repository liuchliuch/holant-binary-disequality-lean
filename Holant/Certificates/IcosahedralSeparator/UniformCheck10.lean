import Holant.Certificates.IcosahedralSeparator.UniformCheck09

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_10 : UniformRankCheck 10 := by decide +kernel
theorem uniformOutsideCheck_10 : UniformOutsideCheck 10 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
