import Holant.Certificates.TwelveLoops.CountsData

namespace Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem block320 : blockHistogram (3,2,0)=printedBlocks (3,2,0) := by decide

theorem block321 : blockHistogram (3,2,1)=printedBlocks (3,2,1) := by decide

theorem block322 : blockHistogram (3,2,2)=printedBlocks (3,2,2) := by decide

theorem block323 : blockHistogram (3,2,3)=printedBlocks (3,2,3) := by decide

theorem block330 : blockHistogram (3,3,0)=printedBlocks (3,3,0) := by decide

theorem block331 : blockHistogram (3,3,1)=printedBlocks (3,3,1) := by decide

theorem block332 : blockHistogram (3,3,2)=printedBlocks (3,3,2) := by decide

theorem block333 : blockHistogram (3,3,3)=printedBlocks (3,3,3) := by decide

end Holant.Certificates.TwelveLoops
