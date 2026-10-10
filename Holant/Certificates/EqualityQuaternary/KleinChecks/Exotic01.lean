import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exoticCardsCorrect01 : ∀ ctx out a,
    cards .exotic 1 ctx out a=cardFormula .exotic 1 ctx out a := by decide +kernel

theorem exoticTargetsCorrect01 : ∀ j,
    targets .exotic 1 j=List.ofFn (targetFormula .exotic 1 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
