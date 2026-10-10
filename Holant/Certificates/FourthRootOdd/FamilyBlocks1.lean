import Holant.Certificates.FourthRootOdd.FamilyData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem family_recover_020 : ∀ b : BState, phaseTest ((0,2,0),b) 0 →
    ((0,2,0),b)=familyState (recoverFamily ((0,2,0),b) 0) := by decide

theorem family_recover_021 : ∀ b : BState, phaseTest ((0,2,1),b) 0 →
    ((0,2,1),b)=familyState (recoverFamily ((0,2,1),b) 0) := by decide

theorem family_recover_022 : ∀ b : BState, phaseTest ((0,2,2),b) 0 →
    ((0,2,2),b)=familyState (recoverFamily ((0,2,2),b) 0) := by decide

theorem family_recover_023 : ∀ b : BState, phaseTest ((0,2,3),b) 0 →
    ((0,2,3),b)=familyState (recoverFamily ((0,2,3),b) 0) := by decide

theorem family_recover_030 : ∀ b : BState, phaseTest ((0,3,0),b) 0 →
    ((0,3,0),b)=familyState (recoverFamily ((0,3,0),b) 0) := by decide

theorem family_recover_031 : ∀ b : BState, phaseTest ((0,3,1),b) 0 →
    ((0,3,1),b)=familyState (recoverFamily ((0,3,1),b) 0) := by decide

theorem family_recover_032 : ∀ b : BState, phaseTest ((0,3,2),b) 0 →
    ((0,3,2),b)=familyState (recoverFamily ((0,3,2),b) 0) := by decide

theorem family_recover_033 : ∀ b : BState, phaseTest ((0,3,3),b) 0 →
    ((0,3,3),b)=familyState (recoverFamily ((0,3,3),b) 0) := by decide

end Holant.Certificates.FourthRootOdd
