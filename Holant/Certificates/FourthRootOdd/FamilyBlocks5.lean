import Holant.Certificates.FourthRootOdd.FamilyData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem family_recover_220 : ∀ b : BState, phaseTest ((2,2,0),b) 0 →
    ((2,2,0),b)=familyState (recoverFamily ((2,2,0),b) 0) := by decide

theorem family_recover_221 : ∀ b : BState, phaseTest ((2,2,1),b) 0 →
    ((2,2,1),b)=familyState (recoverFamily ((2,2,1),b) 0) := by decide

theorem family_recover_222 : ∀ b : BState, phaseTest ((2,2,2),b) 0 →
    ((2,2,2),b)=familyState (recoverFamily ((2,2,2),b) 0) := by decide

theorem family_recover_223 : ∀ b : BState, phaseTest ((2,2,3),b) 0 →
    ((2,2,3),b)=familyState (recoverFamily ((2,2,3),b) 0) := by decide

theorem family_recover_230 : ∀ b : BState, phaseTest ((2,3,0),b) 0 →
    ((2,3,0),b)=familyState (recoverFamily ((2,3,0),b) 0) := by decide

theorem family_recover_231 : ∀ b : BState, phaseTest ((2,3,1),b) 0 →
    ((2,3,1),b)=familyState (recoverFamily ((2,3,1),b) 0) := by decide

theorem family_recover_232 : ∀ b : BState, phaseTest ((2,3,2),b) 0 →
    ((2,3,2),b)=familyState (recoverFamily ((2,3,2),b) 0) := by decide

theorem family_recover_233 : ∀ b : BState, phaseTest ((2,3,3),b) 0 →
    ((2,3,3),b)=familyState (recoverFamily ((2,3,3),b) 0) := by decide

end Holant.Certificates.FourthRootOdd
