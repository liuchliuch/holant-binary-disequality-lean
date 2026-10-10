import Holant.Certificates.FourthRootOdd.FamilyData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem family_recover_100 : ∀ b : BState, phaseTest ((1,0,0),b) 0 →
    ((1,0,0),b)=familyState (recoverFamily ((1,0,0),b) 0) := by decide

theorem family_recover_101 : ∀ b : BState, phaseTest ((1,0,1),b) 0 →
    ((1,0,1),b)=familyState (recoverFamily ((1,0,1),b) 0) := by decide

theorem family_recover_102 : ∀ b : BState, phaseTest ((1,0,2),b) 0 →
    ((1,0,2),b)=familyState (recoverFamily ((1,0,2),b) 0) := by decide

theorem family_recover_103 : ∀ b : BState, phaseTest ((1,0,3),b) 0 →
    ((1,0,3),b)=familyState (recoverFamily ((1,0,3),b) 0) := by decide

theorem family_recover_110 : ∀ b : BState, phaseTest ((1,1,0),b) 0 →
    ((1,1,0),b)=familyState (recoverFamily ((1,1,0),b) 0) := by decide

theorem family_recover_111 : ∀ b : BState, phaseTest ((1,1,1),b) 0 →
    ((1,1,1),b)=familyState (recoverFamily ((1,1,1),b) 0) := by decide

theorem family_recover_112 : ∀ b : BState, phaseTest ((1,1,2),b) 0 →
    ((1,1,2),b)=familyState (recoverFamily ((1,1,2),b) 0) := by decide

theorem family_recover_113 : ∀ b : BState, phaseTest ((1,1,3),b) 0 →
    ((1,1,3),b)=familyState (recoverFamily ((1,1,3),b) 0) := by decide

end Holant.Certificates.FourthRootOdd
