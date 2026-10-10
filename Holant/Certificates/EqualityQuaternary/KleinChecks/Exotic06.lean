import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exoticCardsCorrect06 : ∀ ctx out a,
    cards .exotic 6 ctx out a=cardFormula .exotic 6 ctx out a := by decide +kernel

theorem exoticTargetsCorrect06 : ∀ j,
    targets .exotic 6 j=List.ofFn (targetFormula .exotic 6 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
