import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exoticCardsCorrect23 : ∀ ctx out a,
    cards .exotic 23 ctx out a=cardFormula .exotic 23 ctx out a := by decide +kernel

theorem exoticTargetsCorrect23 : ∀ j,
    targets .exotic 23 j=List.ofFn (targetFormula .exotic 23 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
