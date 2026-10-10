import Holant.Certificates.IcosahedralSeparator.UniformCheck03

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_04 : UniformRankCheck 4 := by decide +kernel
theorem uniformOutsideCheck_04 : UniformOutsideCheck 4 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
