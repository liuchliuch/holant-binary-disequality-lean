import Holant.Certificates.TwelveLoops.CountsData

namespace Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem block000 : blockHistogram (0,0,0)=printedBlocks (0,0,0) := by decide

theorem block001 : blockHistogram (0,0,1)=printedBlocks (0,0,1) := by decide

theorem block002 : blockHistogram (0,0,2)=printedBlocks (0,0,2) := by decide

theorem block003 : blockHistogram (0,0,3)=printedBlocks (0,0,3) := by decide

theorem block010 : blockHistogram (0,1,0)=printedBlocks (0,1,0) := by decide

theorem block011 : blockHistogram (0,1,1)=printedBlocks (0,1,1) := by decide

theorem block012 : blockHistogram (0,1,2)=printedBlocks (0,1,2) := by decide

theorem block013 : blockHistogram (0,1,3)=printedBlocks (0,1,3) := by decide

end Holant.Certificates.TwelveLoops
