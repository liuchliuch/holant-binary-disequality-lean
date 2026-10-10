import Holant.Certificates.IcosahedralSeparator.UniformCheck07

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_08 : UniformRankCheck 8 := by decide +kernel
theorem uniformOutsideCheck_08 : UniformOutsideCheck 8 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
