import Holant.Certificates.FourthRootOdd.PhaseData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem phase_dispatch_220 : ∀ b : BState, classify ((2,2,0),b)=.remaining →
    ¬Exceptional ((2,2,0),b) → phaseTest ((2,2,0),b) 0 ∨ phaseTest ((2,2,0),b) 1 := by decide

theorem phase_dispatch_221 : ∀ b : BState, classify ((2,2,1),b)=.remaining →
    ¬Exceptional ((2,2,1),b) → phaseTest ((2,2,1),b) 0 ∨ phaseTest ((2,2,1),b) 1 := by decide

theorem phase_dispatch_222 : ∀ b : BState, classify ((2,2,2),b)=.remaining →
    ¬Exceptional ((2,2,2),b) → phaseTest ((2,2,2),b) 0 ∨ phaseTest ((2,2,2),b) 1 := by decide

theorem phase_dispatch_223 : ∀ b : BState, classify ((2,2,3),b)=.remaining →
    ¬Exceptional ((2,2,3),b) → phaseTest ((2,2,3),b) 0 ∨ phaseTest ((2,2,3),b) 1 := by decide

theorem phase_dispatch_230 : ∀ b : BState, classify ((2,3,0),b)=.remaining →
    ¬Exceptional ((2,3,0),b) → phaseTest ((2,3,0),b) 0 ∨ phaseTest ((2,3,0),b) 1 := by decide

theorem phase_dispatch_231 : ∀ b : BState, classify ((2,3,1),b)=.remaining →
    ¬Exceptional ((2,3,1),b) → phaseTest ((2,3,1),b) 0 ∨ phaseTest ((2,3,1),b) 1 := by decide

theorem phase_dispatch_232 : ∀ b : BState, classify ((2,3,2),b)=.remaining →
    ¬Exceptional ((2,3,2),b) → phaseTest ((2,3,2),b) 0 ∨ phaseTest ((2,3,2),b) 1 := by decide

theorem phase_dispatch_233 : ∀ b : BState, classify ((2,3,3),b)=.remaining →
    ¬Exceptional ((2,3,3),b) → phaseTest ((2,3,3),b) 0 ∨ phaseTest ((2,3,3),b) 1 := by decide

end Holant.Certificates.FourthRootOdd
