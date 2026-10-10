import Holant.Certificates.FourthRootOdd.FamilyData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem family_recover_000 : ∀ b : BState, phaseTest ((0,0,0),b) 0 →
    ((0,0,0),b)=familyState (recoverFamily ((0,0,0),b) 0) := by decide

theorem family_recover_001 : ∀ b : BState, phaseTest ((0,0,1),b) 0 →
    ((0,0,1),b)=familyState (recoverFamily ((0,0,1),b) 0) := by decide

theorem family_recover_002 : ∀ b : BState, phaseTest ((0,0,2),b) 0 →
    ((0,0,2),b)=familyState (recoverFamily ((0,0,2),b) 0) := by decide

theorem family_recover_003 : ∀ b : BState, phaseTest ((0,0,3),b) 0 →
    ((0,0,3),b)=familyState (recoverFamily ((0,0,3),b) 0) := by decide

theorem family_recover_010 : ∀ b : BState, phaseTest ((0,1,0),b) 0 →
    ((0,1,0),b)=familyState (recoverFamily ((0,1,0),b) 0) := by decide

theorem family_recover_011 : ∀ b : BState, phaseTest ((0,1,1),b) 0 →
    ((0,1,1),b)=familyState (recoverFamily ((0,1,1),b) 0) := by decide

theorem family_recover_012 : ∀ b : BState, phaseTest ((0,1,2),b) 0 →
    ((0,1,2),b)=familyState (recoverFamily ((0,1,2),b) 0) := by decide

theorem family_recover_013 : ∀ b : BState, phaseTest ((0,1,3),b) 0 →
    ((0,1,3),b)=familyState (recoverFamily ((0,1,3),b) 0) := by decide

end Holant.Certificates.FourthRootOdd
