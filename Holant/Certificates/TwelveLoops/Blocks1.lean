import Holant.Certificates.TwelveLoops.CountsData

namespace Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem block020 : blockHistogram (0,2,0)=printedBlocks (0,2,0) := by decide

theorem block021 : blockHistogram (0,2,1)=printedBlocks (0,2,1) := by decide

theorem block022 : blockHistogram (0,2,2)=printedBlocks (0,2,2) := by decide

theorem block023 : blockHistogram (0,2,3)=printedBlocks (0,2,3) := by decide

theorem block030 : blockHistogram (0,3,0)=printedBlocks (0,3,0) := by decide

theorem block031 : blockHistogram (0,3,1)=printedBlocks (0,3,1) := by decide

theorem block032 : blockHistogram (0,3,2)=printedBlocks (0,3,2) := by decide

theorem block033 : blockHistogram (0,3,3)=printedBlocks (0,3,3) := by decide

end Holant.Certificates.TwelveLoops
