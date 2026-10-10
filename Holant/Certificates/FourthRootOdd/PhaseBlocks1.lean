import Holant.Certificates.FourthRootOdd.PhaseData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem phase_dispatch_020 : ∀ b : BState, classify ((0,2,0),b)=.remaining →
    ¬Exceptional ((0,2,0),b) → phaseTest ((0,2,0),b) 0 ∨ phaseTest ((0,2,0),b) 1 := by decide

theorem phase_dispatch_021 : ∀ b : BState, classify ((0,2,1),b)=.remaining →
    ¬Exceptional ((0,2,1),b) → phaseTest ((0,2,1),b) 0 ∨ phaseTest ((0,2,1),b) 1 := by decide

theorem phase_dispatch_022 : ∀ b : BState, classify ((0,2,2),b)=.remaining →
    ¬Exceptional ((0,2,2),b) → phaseTest ((0,2,2),b) 0 ∨ phaseTest ((0,2,2),b) 1 := by decide

theorem phase_dispatch_023 : ∀ b : BState, classify ((0,2,3),b)=.remaining →
    ¬Exceptional ((0,2,3),b) → phaseTest ((0,2,3),b) 0 ∨ phaseTest ((0,2,3),b) 1 := by decide

theorem phase_dispatch_030 : ∀ b : BState, classify ((0,3,0),b)=.remaining →
    ¬Exceptional ((0,3,0),b) → phaseTest ((0,3,0),b) 0 ∨ phaseTest ((0,3,0),b) 1 := by decide

theorem phase_dispatch_031 : ∀ b : BState, classify ((0,3,1),b)=.remaining →
    ¬Exceptional ((0,3,1),b) → phaseTest ((0,3,1),b) 0 ∨ phaseTest ((0,3,1),b) 1 := by decide

theorem phase_dispatch_032 : ∀ b : BState, classify ((0,3,2),b)=.remaining →
    ¬Exceptional ((0,3,2),b) → phaseTest ((0,3,2),b) 0 ∨ phaseTest ((0,3,2),b) 1 := by decide

theorem phase_dispatch_033 : ∀ b : BState, classify ((0,3,3),b)=.remaining →
    ¬Exceptional ((0,3,3),b) → phaseTest ((0,3,3),b) 0 ∨ phaseTest ((0,3,3),b) 1 := by decide

end Holant.Certificates.FourthRootOdd
