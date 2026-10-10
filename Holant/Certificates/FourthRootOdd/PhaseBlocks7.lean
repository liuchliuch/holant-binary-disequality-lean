import Holant.Certificates.FourthRootOdd.PhaseData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem phase_dispatch_320 : ∀ b : BState, classify ((3,2,0),b)=.remaining →
    ¬Exceptional ((3,2,0),b) → phaseTest ((3,2,0),b) 0 ∨ phaseTest ((3,2,0),b) 1 := by decide

theorem phase_dispatch_321 : ∀ b : BState, classify ((3,2,1),b)=.remaining →
    ¬Exceptional ((3,2,1),b) → phaseTest ((3,2,1),b) 0 ∨ phaseTest ((3,2,1),b) 1 := by decide

theorem phase_dispatch_322 : ∀ b : BState, classify ((3,2,2),b)=.remaining →
    ¬Exceptional ((3,2,2),b) → phaseTest ((3,2,2),b) 0 ∨ phaseTest ((3,2,2),b) 1 := by decide

theorem phase_dispatch_323 : ∀ b : BState, classify ((3,2,3),b)=.remaining →
    ¬Exceptional ((3,2,3),b) → phaseTest ((3,2,3),b) 0 ∨ phaseTest ((3,2,3),b) 1 := by decide

theorem phase_dispatch_330 : ∀ b : BState, classify ((3,3,0),b)=.remaining →
    ¬Exceptional ((3,3,0),b) → phaseTest ((3,3,0),b) 0 ∨ phaseTest ((3,3,0),b) 1 := by decide

theorem phase_dispatch_331 : ∀ b : BState, classify ((3,3,1),b)=.remaining →
    ¬Exceptional ((3,3,1),b) → phaseTest ((3,3,1),b) 0 ∨ phaseTest ((3,3,1),b) 1 := by decide

theorem phase_dispatch_332 : ∀ b : BState, classify ((3,3,2),b)=.remaining →
    ¬Exceptional ((3,3,2),b) → phaseTest ((3,3,2),b) 0 ∨ phaseTest ((3,3,2),b) 1 := by decide

theorem phase_dispatch_333 : ∀ b : BState, classify ((3,3,3),b)=.remaining →
    ¬Exceptional ((3,3,3),b) → phaseTest ((3,3,3),b) 0 ∨ phaseTest ((3,3,3),b) 1 := by decide

end Holant.Certificates.FourthRootOdd
