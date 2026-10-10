import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exoticCardsCorrect07 : ∀ ctx out a,
    cards .exotic 7 ctx out a=cardFormula .exotic 7 ctx out a := by decide +kernel

theorem exoticTargetsCorrect07 : ∀ j,
    targets .exotic 7 j=List.ofFn (targetFormula .exotic 7 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
