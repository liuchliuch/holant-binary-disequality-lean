import Holant.Certificates.IcosahedralSeparator.UniformCheck28

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_29 : UniformRankCheck 29 := by decide +kernel
theorem uniformOutsideCheck_29 : UniformOutsideCheck 29 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
