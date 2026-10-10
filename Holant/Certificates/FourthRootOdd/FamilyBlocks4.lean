import Holant.Certificates.FourthRootOdd.FamilyData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem family_recover_200 : ∀ b : BState, phaseTest ((2,0,0),b) 0 →
    ((2,0,0),b)=familyState (recoverFamily ((2,0,0),b) 0) := by decide

theorem family_recover_201 : ∀ b : BState, phaseTest ((2,0,1),b) 0 →
    ((2,0,1),b)=familyState (recoverFamily ((2,0,1),b) 0) := by decide

theorem family_recover_202 : ∀ b : BState, phaseTest ((2,0,2),b) 0 →
    ((2,0,2),b)=familyState (recoverFamily ((2,0,2),b) 0) := by decide

theorem family_recover_203 : ∀ b : BState, phaseTest ((2,0,3),b) 0 →
    ((2,0,3),b)=familyState (recoverFamily ((2,0,3),b) 0) := by decide

theorem family_recover_210 : ∀ b : BState, phaseTest ((2,1,0),b) 0 →
    ((2,1,0),b)=familyState (recoverFamily ((2,1,0),b) 0) := by decide

theorem family_recover_211 : ∀ b : BState, phaseTest ((2,1,1),b) 0 →
    ((2,1,1),b)=familyState (recoverFamily ((2,1,1),b) 0) := by decide

theorem family_recover_212 : ∀ b : BState, phaseTest ((2,1,2),b) 0 →
    ((2,1,2),b)=familyState (recoverFamily ((2,1,2),b) 0) := by decide

theorem family_recover_213 : ∀ b : BState, phaseTest ((2,1,3),b) 0 →
    ((2,1,3),b)=familyState (recoverFamily ((2,1,3),b) 0) := by decide

end Holant.Certificates.FourthRootOdd
