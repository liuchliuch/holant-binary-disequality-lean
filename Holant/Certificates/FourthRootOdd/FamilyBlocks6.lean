import Holant.Certificates.FourthRootOdd.FamilyData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem family_recover_300 : ∀ b : BState, phaseTest ((3,0,0),b) 0 →
    ((3,0,0),b)=familyState (recoverFamily ((3,0,0),b) 0) := by decide

theorem family_recover_301 : ∀ b : BState, phaseTest ((3,0,1),b) 0 →
    ((3,0,1),b)=familyState (recoverFamily ((3,0,1),b) 0) := by decide

theorem family_recover_302 : ∀ b : BState, phaseTest ((3,0,2),b) 0 →
    ((3,0,2),b)=familyState (recoverFamily ((3,0,2),b) 0) := by decide

theorem family_recover_303 : ∀ b : BState, phaseTest ((3,0,3),b) 0 →
    ((3,0,3),b)=familyState (recoverFamily ((3,0,3),b) 0) := by decide

theorem family_recover_310 : ∀ b : BState, phaseTest ((3,1,0),b) 0 →
    ((3,1,0),b)=familyState (recoverFamily ((3,1,0),b) 0) := by decide

theorem family_recover_311 : ∀ b : BState, phaseTest ((3,1,1),b) 0 →
    ((3,1,1),b)=familyState (recoverFamily ((3,1,1),b) 0) := by decide

theorem family_recover_312 : ∀ b : BState, phaseTest ((3,1,2),b) 0 →
    ((3,1,2),b)=familyState (recoverFamily ((3,1,2),b) 0) := by decide

theorem family_recover_313 : ∀ b : BState, phaseTest ((3,1,3),b) 0 →
    ((3,1,3),b)=familyState (recoverFamily ((3,1,3),b) 0) := by decide

end Holant.Certificates.FourthRootOdd
