import Holant.Certificates.TwelveLoops.CountsData

namespace Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem block100 : blockHistogram (1,0,0)=printedBlocks (1,0,0) := by decide

theorem block101 : blockHistogram (1,0,1)=printedBlocks (1,0,1) := by decide

theorem block102 : blockHistogram (1,0,2)=printedBlocks (1,0,2) := by decide

theorem block103 : blockHistogram (1,0,3)=printedBlocks (1,0,3) := by decide

theorem block110 : blockHistogram (1,1,0)=printedBlocks (1,1,0) := by decide

theorem block111 : blockHistogram (1,1,1)=printedBlocks (1,1,1) := by decide

theorem block112 : blockHistogram (1,1,2)=printedBlocks (1,1,2) := by decide

theorem block113 : blockHistogram (1,1,3)=printedBlocks (1,1,3) := by decide

end Holant.Certificates.TwelveLoops
