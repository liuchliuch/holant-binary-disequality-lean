import Holant.Certificates.FourthRootOdd.PhaseData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem phase_dispatch_120 : ∀ b : BState, classify ((1,2,0),b)=.remaining →
    ¬Exceptional ((1,2,0),b) → phaseTest ((1,2,0),b) 0 ∨ phaseTest ((1,2,0),b) 1 := by decide

theorem phase_dispatch_121 : ∀ b : BState, classify ((1,2,1),b)=.remaining →
    ¬Exceptional ((1,2,1),b) → phaseTest ((1,2,1),b) 0 ∨ phaseTest ((1,2,1),b) 1 := by decide

theorem phase_dispatch_122 : ∀ b : BState, classify ((1,2,2),b)=.remaining →
    ¬Exceptional ((1,2,2),b) → phaseTest ((1,2,2),b) 0 ∨ phaseTest ((1,2,2),b) 1 := by decide

theorem phase_dispatch_123 : ∀ b : BState, classify ((1,2,3),b)=.remaining →
    ¬Exceptional ((1,2,3),b) → phaseTest ((1,2,3),b) 0 ∨ phaseTest ((1,2,3),b) 1 := by decide

theorem phase_dispatch_130 : ∀ b : BState, classify ((1,3,0),b)=.remaining →
    ¬Exceptional ((1,3,0),b) → phaseTest ((1,3,0),b) 0 ∨ phaseTest ((1,3,0),b) 1 := by decide

theorem phase_dispatch_131 : ∀ b : BState, classify ((1,3,1),b)=.remaining →
    ¬Exceptional ((1,3,1),b) → phaseTest ((1,3,1),b) 0 ∨ phaseTest ((1,3,1),b) 1 := by decide

theorem phase_dispatch_132 : ∀ b : BState, classify ((1,3,2),b)=.remaining →
    ¬Exceptional ((1,3,2),b) → phaseTest ((1,3,2),b) 0 ∨ phaseTest ((1,3,2),b) 1 := by decide

theorem phase_dispatch_133 : ∀ b : BState, classify ((1,3,3),b)=.remaining →
    ¬Exceptional ((1,3,3),b) → phaseTest ((1,3,3),b) 0 ∨ phaseTest ((1,3,3),b) 1 := by decide

end Holant.Certificates.FourthRootOdd
