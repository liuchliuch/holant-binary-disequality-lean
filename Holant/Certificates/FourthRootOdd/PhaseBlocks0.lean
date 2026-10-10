import Holant.Certificates.FourthRootOdd.PhaseData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem phase_dispatch_000 : ∀ b : BState, classify ((0,0,0),b)=.remaining →
    ¬Exceptional ((0,0,0),b) → phaseTest ((0,0,0),b) 0 ∨ phaseTest ((0,0,0),b) 1 := by decide

theorem phase_dispatch_001 : ∀ b : BState, classify ((0,0,1),b)=.remaining →
    ¬Exceptional ((0,0,1),b) → phaseTest ((0,0,1),b) 0 ∨ phaseTest ((0,0,1),b) 1 := by decide

theorem phase_dispatch_002 : ∀ b : BState, classify ((0,0,2),b)=.remaining →
    ¬Exceptional ((0,0,2),b) → phaseTest ((0,0,2),b) 0 ∨ phaseTest ((0,0,2),b) 1 := by decide

theorem phase_dispatch_003 : ∀ b : BState, classify ((0,0,3),b)=.remaining →
    ¬Exceptional ((0,0,3),b) → phaseTest ((0,0,3),b) 0 ∨ phaseTest ((0,0,3),b) 1 := by decide

theorem phase_dispatch_010 : ∀ b : BState, classify ((0,1,0),b)=.remaining →
    ¬Exceptional ((0,1,0),b) → phaseTest ((0,1,0),b) 0 ∨ phaseTest ((0,1,0),b) 1 := by decide

theorem phase_dispatch_011 : ∀ b : BState, classify ((0,1,1),b)=.remaining →
    ¬Exceptional ((0,1,1),b) → phaseTest ((0,1,1),b) 0 ∨ phaseTest ((0,1,1),b) 1 := by decide

theorem phase_dispatch_012 : ∀ b : BState, classify ((0,1,2),b)=.remaining →
    ¬Exceptional ((0,1,2),b) → phaseTest ((0,1,2),b) 0 ∨ phaseTest ((0,1,2),b) 1 := by decide

theorem phase_dispatch_013 : ∀ b : BState, classify ((0,1,3),b)=.remaining →
    ¬Exceptional ((0,1,3),b) → phaseTest ((0,1,3),b) 0 ∨ phaseTest ((0,1,3),b) 1 := by decide

end Holant.Certificates.FourthRootOdd
