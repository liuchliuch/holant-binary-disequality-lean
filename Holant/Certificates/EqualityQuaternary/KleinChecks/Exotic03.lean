import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exoticCardsCorrect03 : ∀ ctx out a,
    cards .exotic 3 ctx out a=cardFormula .exotic 3 ctx out a := by decide +kernel

theorem exoticTargetsCorrect03 : ∀ j,
    targets .exotic 3 j=List.ofFn (targetFormula .exotic 3 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
