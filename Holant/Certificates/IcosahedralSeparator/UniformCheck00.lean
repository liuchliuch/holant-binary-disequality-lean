import Holant.Certificates.IcosahedralSeparator.UniformPredicates

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option Elab.async false

theorem uniformRankCheck_00 : UniformRankCheck 0 := by decide +kernel
theorem uniformOutsideCheck_00 : UniformOutsideCheck 0 := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
