import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem standardCardsCorrect00 : ∀ ctx out a,
    cards .standard 0 ctx out a=cardFormula .standard 0 ctx out a := by decide +kernel

theorem standardTargetsCorrect00 : ∀ j,
    targets .standard 0 j=List.ofFn (targetFormula .standard 0 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
