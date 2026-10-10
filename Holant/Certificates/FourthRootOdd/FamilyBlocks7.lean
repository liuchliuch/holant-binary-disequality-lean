import Holant.Certificates.FourthRootOdd.FamilyData

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem family_recover_320 : ∀ b : BState, phaseTest ((3,2,0),b) 0 →
    ((3,2,0),b)=familyState (recoverFamily ((3,2,0),b) 0) := by decide

theorem family_recover_321 : ∀ b : BState, phaseTest ((3,2,1),b) 0 →
    ((3,2,1),b)=familyState (recoverFamily ((3,2,1),b) 0) := by decide

theorem family_recover_322 : ∀ b : BState, phaseTest ((3,2,2),b) 0 →
    ((3,2,2),b)=familyState (recoverFamily ((3,2,2),b) 0) := by decide

theorem family_recover_323 : ∀ b : BState, phaseTest ((3,2,3),b) 0 →
    ((3,2,3),b)=familyState (recoverFamily ((3,2,3),b) 0) := by decide

theorem family_recover_330 : ∀ b : BState, phaseTest ((3,3,0),b) 0 →
    ((3,3,0),b)=familyState (recoverFamily ((3,3,0),b) 0) := by decide

theorem family_recover_331 : ∀ b : BState, phaseTest ((3,3,1),b) 0 →
    ((3,3,1),b)=familyState (recoverFamily ((3,3,1),b) 0) := by decide

theorem family_recover_332 : ∀ b : BState, phaseTest ((3,3,2),b) 0 →
    ((3,3,2),b)=familyState (recoverFamily ((3,3,2),b) 0) := by decide

theorem family_recover_333 : ∀ b : BState, phaseTest ((3,3,3),b) 0 →
    ((3,3,3),b)=familyState (recoverFamily ((3,3,3),b) 0) := by decide

end Holant.Certificates.FourthRootOdd
