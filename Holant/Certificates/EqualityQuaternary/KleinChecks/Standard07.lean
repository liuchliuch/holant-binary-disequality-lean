import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem standardCardsCorrect07 : ∀ ctx out a,
    cards .standard 7 ctx out a=cardFormula .standard 7 ctx out a := by decide +kernel

theorem standardTargetsCorrect07 : ∀ j,
    targets .standard 7 j=List.ofFn (targetFormula .standard 7 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
