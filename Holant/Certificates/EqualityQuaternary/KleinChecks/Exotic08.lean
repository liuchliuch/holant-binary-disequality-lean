import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exoticCardsCorrect08 : ∀ ctx out a,
    cards .exotic 8 ctx out a=cardFormula .exotic 8 ctx out a := by decide +kernel

theorem exoticTargetsCorrect08 : ∀ j,
    targets .exotic 8 j=List.ofFn (targetFormula .exotic 8 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
