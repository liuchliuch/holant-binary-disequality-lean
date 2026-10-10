import Holant.Certificates.TwelveLoops.CountsData

namespace Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem block200 : blockHistogram (2,0,0)=printedBlocks (2,0,0) := by decide

theorem block201 : blockHistogram (2,0,1)=printedBlocks (2,0,1) := by decide

theorem block202 : blockHistogram (2,0,2)=printedBlocks (2,0,2) := by decide

theorem block203 : blockHistogram (2,0,3)=printedBlocks (2,0,3) := by decide

theorem block210 : blockHistogram (2,1,0)=printedBlocks (2,1,0) := by decide

theorem block211 : blockHistogram (2,1,1)=printedBlocks (2,1,1) := by decide

theorem block212 : blockHistogram (2,1,2)=printedBlocks (2,1,2) := by decide

theorem block213 : blockHistogram (2,1,3)=printedBlocks (2,1,3) := by decide

end Holant.Certificates.TwelveLoops
