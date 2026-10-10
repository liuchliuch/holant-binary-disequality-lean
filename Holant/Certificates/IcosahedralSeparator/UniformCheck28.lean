import Holant.Certificates.IcosahedralSeparator.UniformCheck27

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_28 : UniformRankCheck 28 := by decide +kernel
theorem uniformOutsideCheck_28 : UniformOutsideCheck 28 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
