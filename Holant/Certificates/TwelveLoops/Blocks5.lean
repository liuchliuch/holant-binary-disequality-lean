import Holant.Certificates.TwelveLoops.CountsData

namespace Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem block220 : blockHistogram (2,2,0)=printedBlocks (2,2,0) := by decide

theorem block221 : blockHistogram (2,2,1)=printedBlocks (2,2,1) := by decide

theorem block222 : blockHistogram (2,2,2)=printedBlocks (2,2,2) := by decide

theorem block223 : blockHistogram (2,2,3)=printedBlocks (2,2,3) := by decide

theorem block230 : blockHistogram (2,3,0)=printedBlocks (2,3,0) := by decide

theorem block231 : blockHistogram (2,3,1)=printedBlocks (2,3,1) := by decide

theorem block232 : blockHistogram (2,3,2)=printedBlocks (2,3,2) := by decide

theorem block233 : blockHistogram (2,3,3)=printedBlocks (2,3,3) := by decide

end Holant.Certificates.TwelveLoops
