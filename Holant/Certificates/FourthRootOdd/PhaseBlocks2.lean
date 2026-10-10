import Holant.Certificates.FourthRootOdd.PhaseData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem phase_dispatch_100 : ∀ b : BState, classify ((1,0,0),b)=.remaining →
    ¬Exceptional ((1,0,0),b) → phaseTest ((1,0,0),b) 0 ∨ phaseTest ((1,0,0),b) 1 := by decide

theorem phase_dispatch_101 : ∀ b : BState, classify ((1,0,1),b)=.remaining →
    ¬Exceptional ((1,0,1),b) → phaseTest ((1,0,1),b) 0 ∨ phaseTest ((1,0,1),b) 1 := by decide

theorem phase_dispatch_102 : ∀ b : BState, classify ((1,0,2),b)=.remaining →
    ¬Exceptional ((1,0,2),b) → phaseTest ((1,0,2),b) 0 ∨ phaseTest ((1,0,2),b) 1 := by decide

theorem phase_dispatch_103 : ∀ b : BState, classify ((1,0,3),b)=.remaining →
    ¬Exceptional ((1,0,3),b) → phaseTest ((1,0,3),b) 0 ∨ phaseTest ((1,0,3),b) 1 := by decide

theorem phase_dispatch_110 : ∀ b : BState, classify ((1,1,0),b)=.remaining →
    ¬Exceptional ((1,1,0),b) → phaseTest ((1,1,0),b) 0 ∨ phaseTest ((1,1,0),b) 1 := by decide

theorem phase_dispatch_111 : ∀ b : BState, classify ((1,1,1),b)=.remaining →
    ¬Exceptional ((1,1,1),b) → phaseTest ((1,1,1),b) 0 ∨ phaseTest ((1,1,1),b) 1 := by decide

theorem phase_dispatch_112 : ∀ b : BState, classify ((1,1,2),b)=.remaining →
    ¬Exceptional ((1,1,2),b) → phaseTest ((1,1,2),b) 0 ∨ phaseTest ((1,1,2),b) 1 := by decide

theorem phase_dispatch_113 : ∀ b : BState, classify ((1,1,3),b)=.remaining →
    ¬Exceptional ((1,1,3),b) → phaseTest ((1,1,3),b) 0 ∨ phaseTest ((1,1,3),b) 1 := by decide

end Holant.Certificates.FourthRootOdd
