import Holant.Certificates.IcosahedralSeparator.UniformCheck15

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_16 : UniformRankCheck 16 := by decide +kernel
theorem uniformOutsideCheck_16 : UniformOutsideCheck 16 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
