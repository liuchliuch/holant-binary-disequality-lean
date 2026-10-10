import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exoticCardsCorrect09 : ∀ ctx out a,
    cards .exotic 9 ctx out a=cardFormula .exotic 9 ctx out a := by decide +kernel

theorem exoticTargetsCorrect09 : ∀ j,
    targets .exotic 9 j=List.ofFn (targetFormula .exotic 9 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
