import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exoticCardsCorrect02 : ∀ ctx out a,
    cards .exotic 2 ctx out a=cardFormula .exotic 2 ctx out a := by decide +kernel

theorem exoticTargetsCorrect02 : ∀ j,
    targets .exotic 2 j=List.ofFn (targetFormula .exotic 2 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
