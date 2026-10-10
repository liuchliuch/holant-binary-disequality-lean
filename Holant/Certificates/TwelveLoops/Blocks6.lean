import Holant.Certificates.TwelveLoops.CountsData

namespace Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem block300 : blockHistogram (3,0,0)=printedBlocks (3,0,0) := by decide

theorem block301 : blockHistogram (3,0,1)=printedBlocks (3,0,1) := by decide

theorem block302 : blockHistogram (3,0,2)=printedBlocks (3,0,2) := by decide

theorem block303 : blockHistogram (3,0,3)=printedBlocks (3,0,3) := by decide

theorem block310 : blockHistogram (3,1,0)=printedBlocks (3,1,0) := by decide

theorem block311 : blockHistogram (3,1,1)=printedBlocks (3,1,1) := by decide

theorem block312 : blockHistogram (3,1,2)=printedBlocks (3,1,2) := by decide

theorem block313 : blockHistogram (3,1,3)=printedBlocks (3,1,3) := by decide

end Holant.Certificates.TwelveLoops
