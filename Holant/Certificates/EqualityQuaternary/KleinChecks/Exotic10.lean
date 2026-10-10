import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exoticCardsCorrect10 : ∀ ctx out a,
    cards .exotic 10 ctx out a=cardFormula .exotic 10 ctx out a := by decide +kernel

theorem exoticTargetsCorrect10 : ∀ j,
    targets .exotic 10 j=List.ofFn (targetFormula .exotic 10 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
