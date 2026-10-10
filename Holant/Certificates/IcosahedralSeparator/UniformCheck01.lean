import Holant.Certificates.IcosahedralSeparator.UniformCheck00

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_01 : UniformRankCheck 1 := by decide +kernel
theorem uniformOutsideCheck_01 : UniformOutsideCheck 1 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
