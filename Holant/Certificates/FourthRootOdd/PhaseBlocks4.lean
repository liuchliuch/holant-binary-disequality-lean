import Holant.Certificates.FourthRootOdd.PhaseData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem phase_dispatch_200 : ∀ b : BState, classify ((2,0,0),b)=.remaining →
    ¬Exceptional ((2,0,0),b) → phaseTest ((2,0,0),b) 0 ∨ phaseTest ((2,0,0),b) 1 := by decide

theorem phase_dispatch_201 : ∀ b : BState, classify ((2,0,1),b)=.remaining →
    ¬Exceptional ((2,0,1),b) → phaseTest ((2,0,1),b) 0 ∨ phaseTest ((2,0,1),b) 1 := by decide

theorem phase_dispatch_202 : ∀ b : BState, classify ((2,0,2),b)=.remaining →
    ¬Exceptional ((2,0,2),b) → phaseTest ((2,0,2),b) 0 ∨ phaseTest ((2,0,2),b) 1 := by decide

theorem phase_dispatch_203 : ∀ b : BState, classify ((2,0,3),b)=.remaining →
    ¬Exceptional ((2,0,3),b) → phaseTest ((2,0,3),b) 0 ∨ phaseTest ((2,0,3),b) 1 := by decide

theorem phase_dispatch_210 : ∀ b : BState, classify ((2,1,0),b)=.remaining →
    ¬Exceptional ((2,1,0),b) → phaseTest ((2,1,0),b) 0 ∨ phaseTest ((2,1,0),b) 1 := by decide

theorem phase_dispatch_211 : ∀ b : BState, classify ((2,1,1),b)=.remaining →
    ¬Exceptional ((2,1,1),b) → phaseTest ((2,1,1),b) 0 ∨ phaseTest ((2,1,1),b) 1 := by decide

theorem phase_dispatch_212 : ∀ b : BState, classify ((2,1,2),b)=.remaining →
    ¬Exceptional ((2,1,2),b) → phaseTest ((2,1,2),b) 0 ∨ phaseTest ((2,1,2),b) 1 := by decide

theorem phase_dispatch_213 : ∀ b : BState, classify ((2,1,3),b)=.remaining →
    ¬Exceptional ((2,1,3),b) → phaseTest ((2,1,3),b) 0 ∨ phaseTest ((2,1,3),b) 1 := by decide

end Holant.Certificates.FourthRootOdd
