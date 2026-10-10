import Holant.Certificates.FourthRootOdd.PhaseData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem phase_dispatch_300 : ∀ b : BState, classify ((3,0,0),b)=.remaining →
    ¬Exceptional ((3,0,0),b) → phaseTest ((3,0,0),b) 0 ∨ phaseTest ((3,0,0),b) 1 := by decide

theorem phase_dispatch_301 : ∀ b : BState, classify ((3,0,1),b)=.remaining →
    ¬Exceptional ((3,0,1),b) → phaseTest ((3,0,1),b) 0 ∨ phaseTest ((3,0,1),b) 1 := by decide

theorem phase_dispatch_302 : ∀ b : BState, classify ((3,0,2),b)=.remaining →
    ¬Exceptional ((3,0,2),b) → phaseTest ((3,0,2),b) 0 ∨ phaseTest ((3,0,2),b) 1 := by decide

theorem phase_dispatch_303 : ∀ b : BState, classify ((3,0,3),b)=.remaining →
    ¬Exceptional ((3,0,3),b) → phaseTest ((3,0,3),b) 0 ∨ phaseTest ((3,0,3),b) 1 := by decide

theorem phase_dispatch_310 : ∀ b : BState, classify ((3,1,0),b)=.remaining →
    ¬Exceptional ((3,1,0),b) → phaseTest ((3,1,0),b) 0 ∨ phaseTest ((3,1,0),b) 1 := by decide

theorem phase_dispatch_311 : ∀ b : BState, classify ((3,1,1),b)=.remaining →
    ¬Exceptional ((3,1,1),b) → phaseTest ((3,1,1),b) 0 ∨ phaseTest ((3,1,1),b) 1 := by decide

theorem phase_dispatch_312 : ∀ b : BState, classify ((3,1,2),b)=.remaining →
    ¬Exceptional ((3,1,2),b) → phaseTest ((3,1,2),b) 0 ∨ phaseTest ((3,1,2),b) 1 := by decide

theorem phase_dispatch_313 : ∀ b : BState, classify ((3,1,3),b)=.remaining →
    ¬Exceptional ((3,1,3),b) → phaseTest ((3,1,3),b) 0 ∨ phaseTest ((3,1,3),b) 1 := by decide

end Holant.Certificates.FourthRootOdd
