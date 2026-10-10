import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exoticCardsCorrect00 : ∀ ctx out a,
    cards .exotic 0 ctx out a=cardFormula .exotic 0 ctx out a := by decide +kernel

theorem exoticTargetsCorrect00 : ∀ j,
    targets .exotic 0 j=List.ofFn (targetFormula .exotic 0 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
