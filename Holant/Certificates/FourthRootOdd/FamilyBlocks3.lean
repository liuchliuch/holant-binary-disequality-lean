import Holant.Certificates.FourthRootOdd.FamilyData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem family_recover_120 : ∀ b : BState, phaseTest ((1,2,0),b) 0 →
    ((1,2,0),b)=familyState (recoverFamily ((1,2,0),b) 0) := by decide

theorem family_recover_121 : ∀ b : BState, phaseTest ((1,2,1),b) 0 →
    ((1,2,1),b)=familyState (recoverFamily ((1,2,1),b) 0) := by decide

theorem family_recover_122 : ∀ b : BState, phaseTest ((1,2,2),b) 0 →
    ((1,2,2),b)=familyState (recoverFamily ((1,2,2),b) 0) := by decide

theorem family_recover_123 : ∀ b : BState, phaseTest ((1,2,3),b) 0 →
    ((1,2,3),b)=familyState (recoverFamily ((1,2,3),b) 0) := by decide

theorem family_recover_130 : ∀ b : BState, phaseTest ((1,3,0),b) 0 →
    ((1,3,0),b)=familyState (recoverFamily ((1,3,0),b) 0) := by decide

theorem family_recover_131 : ∀ b : BState, phaseTest ((1,3,1),b) 0 →
    ((1,3,1),b)=familyState (recoverFamily ((1,3,1),b) 0) := by decide

theorem family_recover_132 : ∀ b : BState, phaseTest ((1,3,2),b) 0 →
    ((1,3,2),b)=familyState (recoverFamily ((1,3,2),b) 0) := by decide

theorem family_recover_133 : ∀ b : BState, phaseTest ((1,3,3),b) 0 →
    ((1,3,3),b)=familyState (recoverFamily ((1,3,3),b) 0) := by decide

end Holant.Certificates.FourthRootOdd
