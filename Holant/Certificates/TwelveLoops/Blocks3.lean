import Holant.Certificates.TwelveLoops.CountsData

namespace Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem block120 : blockHistogram (1,2,0)=printedBlocks (1,2,0) := by decide

theorem block121 : blockHistogram (1,2,1)=printedBlocks (1,2,1) := by decide

theorem block122 : blockHistogram (1,2,2)=printedBlocks (1,2,2) := by decide

theorem block123 : blockHistogram (1,2,3)=printedBlocks (1,2,3) := by decide

theorem block130 : blockHistogram (1,3,0)=printedBlocks (1,3,0) := by decide

theorem block131 : blockHistogram (1,3,1)=printedBlocks (1,3,1) := by decide

theorem block132 : blockHistogram (1,3,2)=printedBlocks (1,3,2) := by decide

theorem block133 : blockHistogram (1,3,3)=printedBlocks (1,3,3) := by decide

end Holant.Certificates.TwelveLoops
