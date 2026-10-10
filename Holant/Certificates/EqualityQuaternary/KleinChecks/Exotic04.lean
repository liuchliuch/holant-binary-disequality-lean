import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exoticCardsCorrect04 : ∀ ctx out a,
    cards .exotic 4 ctx out a=cardFormula .exotic 4 ctx out a := by decide +kernel

theorem exoticTargetsCorrect04 : ∀ j,
    targets .exotic 4 j=List.ofFn (targetFormula .exotic 4 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
